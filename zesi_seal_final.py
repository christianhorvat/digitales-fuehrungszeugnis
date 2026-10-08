#!/usr/bin/env python3
"""
zesi_seal.py - zerlegt den Rohinhalt eines Digital-Seal-QR-Codes (Format nach
jg.f.a(byte[]) der ZeSI-App) und prueft die Signatur gegen die Zertifikate
aus assets/certificates-prod/.

Eingabe (genau eine):
  --image bild.png   QR-Bild (OpenCV; braucht eine Version mit detectAndDecodeBytes)
  --bin datei.bin    Rohbytes
  --hex 'dc03...'    Hex-String
  --b64 '...'        Base64-String

Zertifikate:
  --certs ordner     Ordner mit certificates.json und den .cer-Dateien

Abhaengigkeiten: pip install cryptography   (Bild-Modus zusaetzlich: opencv-python)
Format und Pruefung aus dem dekompilierten Code rekonstruiert; erfolgreich gegen ein
echtes, gueltig signiertes Fuehrungszeugnis-Siegel getestet (BFJ-Produktivzertifikat).
"""
import argparse, base64, datetime, hashlib, json, pathlib, sys

from cryptography import x509
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, padding, utils

# C40-Tabelle (Standard): 3=Leerzeichen, 4-13=0-9, 14-39=A-Z; 0-2 = Shift, ergibt kein Zeichen
C40 = {3: " "}
C40.update({4 + i: str(i) for i in range(10)})
C40.update({14 + i: chr(65 + i) for i in range(26)})

TYPES = {
    (1, 93): "VISA",
    (2, 253): "ARRIVAL_ATTESTATION",
    (6, 251): "RESIDENCE_PERMIT",
    (6, 250): "RESIDENCE_PERMIT_SUPPLEMENTARY_SHEET",
    (8, 249): "ADDRESS_STICKER_FOR_ID",
    (12, 249): "ADDRESS_STICKER_FOR_EAT",
    (10, 248): "PLACE_OF_RESIDENCE_STICKER_FOR_PASSPORT",
    (200, 1): "jg.b (Uhrzeitpruefung uebersprungen; UUID-Feature Tag 0)",
    (201, 1): "jg.b (Uhrzeitpruefung uebersprungen; UUID-Feature Tag 0)",
}


def c40(b):
    if len(b) % 2:
        raise ValueError("C40: ungerade Bytezahl")
    out = ""
    for i in range(0, len(b), 2):
        b0, b1 = b[i], b[i + 1]
        if b0 == 254:                      # ASCII-Escape wie in ba/se.java
            out += chr(b1 - 1)
            continue
        v = b0 * 256 + b1 - 1
        for x in (v // 1600, (v % 1600) // 40, v % 40):
            out += C40.get(x, "")
    return out


def date3(b):
    s = str(int.from_bytes(b, "big")).zfill(8)
    return datetime.datetime.strptime(s, "%m%d%Y").date()


def tlv(buf, ber):
    """ber=True (Version>=4): Laenge ggf. BER-lang, sonst 1 Byte."""
    if len(buf) < 2:
        raise ValueError("TLV zu kurz")
    tag, ln = buf[0], buf[1]
    if not ber or ln <= 127:
        return tag, buf[2:2 + ln], 2 + ln
    n = ln - 128
    if n <= 0 or n == 127:
        raise ValueError("ungueltige Laengenoktette")
    length = int.from_bytes(buf[2:2 + n], "big")
    off = 2 + n
    return tag, buf[off:off + length], off + length


def parse(b):
    r = {"magic": b[0], "version": b[1] + 1}
    ver = r["version"]
    r["country"] = c40(b[2:4]).strip()
    if ver == 4:
        s = c40(b[4:8])
        n = int(float(s[4:]))
        n = n if n > 0 else 2
        blen = -(-n // 3) * 2
        r["signer"], r["ref"] = s[:4], c40(b[8:8 + blen])[:n]
        p = 8 + blen
    else:
        s = c40(b[4:10]).replace("<", "")
        r["signer"], r["ref"] = s[:4], s[4:]
        p = 10
    r["issue"] = date3(b[p:p + 3])
    r["sigdate"] = date3(b[p + 3:p + 6])
    r["b6"], r["b7"] = b[p + 6], b[p + 7]
    r["type"] = TYPES.get((r["b7"], r["b6"]), "jg.c (unbekannt -> App wirft Fehler bei Pruefung 1)")
    p += 8
    feats, q = [], p
    while True:
        if q >= len(b) or q + 1 == len(b):
            raise ValueError("Kein Signatur-Marker (0xFF) gefunden")
        if b[q] == 0xFF:
            break
        tag, val, n = tlv(b[q:], ver >= 4)
        if n <= 0:
            raise ValueError("Feature ohne Fortschritt")
        feats.append((tag, val))
        q += n
    r["features"] = feats
    r["signed"] = b[:q]
    r["sigtag"], r["sig"], _ = tlv(b[q:], ver >= 4)
    return r


def pkup(cert):
    """privateKeyUsagePeriod (2.5.29.16): (notBefore, notAfter) als date oder None."""
    try:
        ext = cert.extensions.get_extension_for_oid(x509.ObjectIdentifier("2.5.29.16"))
    except x509.ExtensionNotFound:
        return None, None
    d = ext.value.value          # DER-SEQUENCE
    res = {0x80: None, 0x81: None}
    i = 2 if d[1] < 128 else 2 + (d[1] - 128)
    while i < len(d):
        t, ln = d[i], d[i + 1]
        v = d[i + 2:i + 2 + ln].decode()
        res[t] = datetime.datetime.strptime(v[:8], "%Y%m%d").date()
        i += 2 + ln
    return res[0x80], res[0x81]


def window(cert):
    """Effektives Fenster wie yf.b: Schnitt aus Zertifikat und PKUP (lokale Zeitzone)."""
    nb = cert.not_valid_before_utc.astimezone().date()
    na = cert.not_valid_after_utc.astimezone().date()
    pb, pa = pkup(cert)
    return (max(nb, pb) if pb else nb), (min(na, pa) if pa else na), (pb, pa)


def verify(cert, msg, sig):
    pk = cert.public_key()
    for hn, h in (("SHA-256", hashes.SHA256()), ("SHA-384", hashes.SHA384()),
                  ("SHA-512", hashes.SHA512()), ("SHA-1", hashes.SHA1())):
        if isinstance(pk, ec.EllipticCurvePublicKey):
            cands = []
            if len(sig) % 2 == 0:
                hf = len(sig) // 2
                cands.append(("raw r||s", utils.encode_dss_signature(
                    int.from_bytes(sig[:hf], "big"), int.from_bytes(sig[hf:], "big"))))
            cands.append(("DER", sig))
            for form, s in cands:
                try:
                    pk.verify(s, msg, ec.ECDSA(h))
                    return f"{hn}withECDSA ({form})"
                except (InvalidSignature, ValueError):
                    pass
        else:
            try:
                pk.verify(sig, msg, padding.PKCS1v15(), h)
                return f"{hn}withRSA (PKCS1v15)"
            except Exception:
                pass
    return None


def load_certs(folder):
    folder = pathlib.Path(folder)
    mapping = json.loads((folder / "certificates.json").read_text(encoding="utf-8"))
    out = []
    for key, fn in mapping.items():
        raw = (folder / fn).read_bytes()
        try:
            c = x509.load_der_x509_certificate(raw)
        except ValueError:
            c = x509.load_pem_x509_certificate(raw)
        signer, _, ref = key.partition("+")
        out.append({"key": key, "signer": signer, "ref": ref, "file": fn, "cert": c,
                    "sha1": hashlib.sha1(c.public_bytes(serialization.Encoding.DER)).hexdigest().upper()})
    return out


def read_input(a):
    if a.hex:
        return bytes.fromhex(a.hex.replace(" ", ""))
    if a.b64:
        return base64.b64decode(a.b64)
    if a.bin:
        return pathlib.Path(a.bin).read_bytes()
    import cv2, numpy as np
    img = cv2.imread(a.image, cv2.IMREAD_GRAYSCALE)
    if img is None:
        sys.exit("Bild nicht lesbar")
    det = cv2.QRCodeDetector()
    if not hasattr(det, "detectAndDecodeBytes"):
        sys.exit("Diese OpenCV-Version liefert keine Rohbytes. Nutze --bin/--hex (z. B. via zbarimg) oder aktualisiere OpenCV.")
    # Auf den eigentlichen Code zuschneiden (hilft bei viel Rand/kleinem Modul-Raster)
    _, bw0 = cv2.threshold(img, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    ys, xs = np.where(bw0 < 128)
    crop = img[ys.min():ys.max() + 1, xs.min():xs.max() + 1] if len(xs) else img
    for blur in (0, 3, 5):
        im = cv2.medianBlur(crop, blur) if blur else crop
        for thmode in ("otsu", "adapt"):
            b = (cv2.threshold(im, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1] if thmode == "otsu"
                 else cv2.adaptiveThreshold(im, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 7))
            for s in (1, 2, 3, 4, 6, 8):
                bb = cv2.copyMakeBorder(b, 40, 40, 40, 40, cv2.BORDER_CONSTANT, value=255)
                if s != 1:
                    bb = cv2.resize(bb, None, fx=s, fy=s, interpolation=cv2.INTER_NEAREST)
                try:
                    data = det.detectAndDecodeBytes(bb)[0]
                except Exception:
                    data = None
                if data:
                    data = bytes(data) if not isinstance(data, str) else data.encode("latin-1")
                    # Bekannter Bug in dieser OpenCV-Python-Bindung: Bytes >=0x80 kommen
                    # UTF-8-codiert zurueck (als waeren sie vorher Latin-1-Codepoints).
                    # Rueckkonvertieren, falls das zutrifft; sonst Rohbytes verwenden.
                    try:
                        fixed = data.decode("utf-8").encode("latin-1")
                        data = fixed
                    except (UnicodeDecodeError, UnicodeEncodeError):
                        pass
                    return data
    sys.exit("QR nicht lesbar")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--image"); g.add_argument("--bin"); g.add_argument("--hex"); g.add_argument("--b64")
    ap.add_argument("--certs", required=True)
    a = ap.parse_args()

    b = read_input(a)
    print(f"Rohdaten: {len(b)} Bytes, erste Bytes: {b[:12].hex()}")
    try:
        r = parse(b)
    except Exception as e:
        sys.exit(f"Kein gueltiger Seal-Header ({type(e).__name__}: {e}) - passt nicht zum erwarteten Format.")

    print(f"Magic 0x{r['magic']:02X}, Version {r['version']}, Land {r['country']!r}")
    print(f"Signer-ID {r['signer']!r}, Referenz {r['ref']!r} ({len(r['ref'])} Zeichen)")
    print(f"Ausgestellt {r['issue']}, Signaturdatum {r['sigdate']}")
    print(f"Typ (Byte+7/Byte+6): {r['b7']}/{r['b6']} -> {r['type']}")
    for tag, val in r["features"]:
        extra = ""
        if len(val) == 16:
            import uuid
            extra = f"  (als UUID: {uuid.UUID(bytes=val)})"
        print(f"  Feature Tag {tag}: {len(val)} Bytes: {val[:24].hex()}{'...' if len(val) > 24 else ''}{extra}")
    print(f"Signatur-Tag 0x{r['sigtag']:02X}, {len(r['sig'])} Bytes; signiert werden {len(r['signed'])} Bytes")
    print(f"MD5 des gesamten Payloads (Dokument-ID der App): {hashlib.md5(b).hexdigest()}")

    certs = load_certs(a.certs)
    print("\nZertifikatssuche:")
    by_key = [c for c in certs if c["signer"] == r["signer"] and c["ref"] == r["ref"]]
    by_sha = [c for c in certs if c["sha1"] == r["ref"]]
    print("  Treffer ueber Signer+Referenz (Mapping):", [c["key"] for c in by_key] or "keiner")
    print("  Treffer ueber SHA-1 (TR-Weg):          ", [c["file"] for c in by_sha] or "keiner")

    print("\nSignaturpruefung (alle Zertifikate, zur Diagnose):")
    for c in certs:
        try:
            res = verify(c["cert"], r["signed"], r["sig"])
            f, t, (pb, pa) = window(c["cert"])
        except Exception as e:
            print(f"  {c['file']}: uebersprungen ({type(e).__name__}: {e})")
            continue
        ok = f <= r["sigdate"] <= t
        print(f"  {c['file']}: Signatur {'OK ' + res if res else 'nein'}; Fenster {f}..{t}"
              f"{' (PKUP ' + str(pb) + '..' + str(pa) + ')' if pb or pa else ''}; Signaturdatum im Fenster: {'ja' if ok else 'NEIN'}")


if __name__ == "__main__":
    main()
