"""Check generated Lean bytes without overwriting any accepted source."""
from pathlib import Path
import runpy,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';original=Path.write_text;checks=[]
def checked_write(path,data,*args,**kwargs):
 if path.suffix=='.lean':
  actual=path.read_text();assert data==actual,str(path)
  checks.append(dict(path=str(path.resolve().relative_to(R)),sha256=hashlib.sha256(data.encode()).hexdigest()))
 return len(data)
Path.write_text=checked_write
try:
 for name in ['generate-guards.py','generate-reserve.py','generate-callers.py','reify-decoders.py','reify-parser-callers.py','reify-chunked.py']:
  runpy.run_path(str(R/'tools/pv-rjdec-20261028'/name),run_name='__main__')
finally:Path.write_text=original
(E/'resume-generator-identity.json').write_text(json.dumps(dict(all_match=True,checks=checks),indent=2)+'\n');print('Generated Lean source identities:',len(checks),'all match')
