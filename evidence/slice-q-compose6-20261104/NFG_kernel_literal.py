"""Deterministic proof-witness repair of the one frozen panic-message literal."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def normalized(raw):
 old='(toStr "cannot invert zero in QM31")'
 assert raw.count(old)==1 and 'NFG_PanicMessage' not in raw
 return raw.replace('import NFG_InverseRef.Types','import NFG_InverseRef.Types\nimport NFG_PanicMessage').replace(old,'NFG_PanicMessage.value')
def check():
 archive=lzma.decompress((E/'NFG_E003_OUTPUTS.json.xz').read_bytes())
 assert sha(archive)==(E/'NFG_E003_OUTPUTS.json.sha256').read_text().strip()
 raw=json.loads(archive)['NFG_row_extracted/NFG_InverseRef/Funs.lean']
 path=E/'NFG_row_extracted/NFG_InverseRef/Funs.lean';assert path.read_text()==normalized(raw)
 data=list(b'cannot invert zero in QM31');message=(E/'NFG_PanicMessage.lean').read_text()
 assert '['+','.join(str(x)+'#u8' for x in data)+']' in message
 assert 'native_decide' not in message and '#print axioms bytes' in message
 return dict(path=str(path.relative_to(E)),before=sha(raw.encode()),after=sha(path.read_bytes()),replacement=['(toStr "cannot invert zero in QM31")','NFG_PanicMessage.value'],bytes=data,byte_length=len(data),reason='L028 native-decide axiom excluded. L031/L032 failed string-proof repairs. L034 checks explicit literal bytes; L035/L036 replay with only standard axioms.',semantic_change='same literal UTF-8 bytes; Option.expect ignores its message in the emitted Result model')
if __name__=='__main__':(E/'NFG_LITERAL_NORMALIZATION.json').write_text(json.dumps(check(),indent=2)+'\n')
