"""Retain accepted objects in own cache; aggregate unchanged attempt receipts."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import hashlib,json,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose11-20261104')
c=b.parent/'codex-cx-slice-s-compose11-cache-20261104/NFH_final_objects_20261104';c.mkdir(exist_ok=True)
for p in (b/'NFH_objects').glob('NFH_*.olean'):
 for src in [p,b/'NFH_generated'/(p.stem+'.lean')]:shutil.copy2(src,c/src.name)
items=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in sorted(c.iterdir()) if p.is_file()]
for p in (b/'NFH_objects').glob('NFH_*.olean'):p.unlink()
print(json.dumps(dict(retained_cache=str(c),files=items,deleted_only='NFH_objects/NFH_*.olean',no_scope_pending=True),indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NFH_FINAL_CACHE.json').write_text(r.stdout)
receipts=[]
for p in sorted(E.glob('NFH_L*/receipt.json')):
 d=json.loads(p.read_text());receipts.append({k:d.get(k) for k in ['attempt','module','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})
(E/'NFH_SECTION6_RECEIPTS.json').write_text(json.dumps(receipts,indent=1)+'\n')
assert len(receipts)==6
for d in receipts[3:]:
 assert d['exit_status']==0 and all('sorryAx' not in s for s in d['print_axioms'])
print('Retained accepted final objects;6 receipts aggregated;L001-L003 excluded')
