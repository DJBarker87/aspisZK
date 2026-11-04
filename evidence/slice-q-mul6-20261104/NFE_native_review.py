"""Run the predecessor's checks unchanged, redirect only the output artifact."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul5-20261104'
s=(P/'NFC_check_native.py').read_text()
old="(E/'NFC_NATIVE_AUDIT.json').write_text"
assert s.count(old)==1
# E must remain the original retained evidence for every validation read.
s=s.replace(old,"(Path("+repr(str(E/'NFE_NATIVE_REVIEW.json'))+")).write_text")
ns={'__file__':str(P/'NFC_check_native.py'),'__name__':'NFE_retained_native_review'}
exec(compile(s,'NFE_retained_native_review','exec'),ns)
(E/'NFE_NATIVE_CHECK_PROVENANCE.json').write_text(json.dumps(dict(source=str(P/'NFC_check_native.py'),source_sha256=hashlib.sha256((P/'NFC_check_native.py').read_bytes()).hexdigest(),change='Output path only; all validation code and evidence inputs unchanged'),indent=2)+'\n')
