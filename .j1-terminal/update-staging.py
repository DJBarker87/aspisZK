from pathlib import Path
import hashlib,json,shutil,re
w=Path(__file__).resolve().parent;m=json.loads((w/'sources/SOURCE-MANIFEST.json').read_text())
repo=w.parent
for n,i in m['modules'].items():
 p=repo/i['source']
 if p.is_file():
  q=w/'sources'/i['stage_as'];shutil.copyfile(p,q)
  i['source_sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
  i['imports']=re.findall(r'^import ([\w.]+)',q.read_text(),re.M)
  i['axiom_requests']=q.read_text().count('#print axioms')
(w/'sources/SOURCE-MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
