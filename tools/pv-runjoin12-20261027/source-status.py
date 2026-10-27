"""Static allocation manifest. Never treat a draft or stale receipt as accepted."""
from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027'
changed=set(subprocess.check_output(['git','diff','--name-only','458a0c1ff2'],cwd=R,text=True).splitlines())
changed.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
rows=[]
for name in sorted(changed):
 p=R/name
 if not p.is_file() or not p.name.startswith('PV_RunJoin_') or p.suffix!='.lean':continue
 raw=p.read_bytes();s=raw.decode();assert not re.search(r'^\s*axiom\b',s,re.M),name
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b',s),name
 sha=hashlib.sha256(raw).hexdigest();module='R1Z/'+p.stem
 matching=[r for r in receipts if r.get('target')==module and r.get('source_sha256')==sha]
 matching.sort(key=lambda r:r['attempt']);r=matching[-1] if matching else None
 rows.append(dict(source=name,sha256=sha,status='accepted' if r and r.get('accepted') else 'not accepted',attempt=r.get('attempt') if r else None,receipt='receipt-'+str(r['attempt'])+'.json' if r else None))
obj=dict(base='458a0c1ff2',revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),files=rows,accepted=sum(r['status']=='accepted' for r in rows),not_accepted=sum(r['status']!='accepted' for r in rows),R_shipped='OPEN: no shipped records extraction constant accepted',target='not established')
(E/'source-status.json').write_text(json.dumps(obj,indent=2)+'\n');print({k:v for k,v in obj.items() if k!='files'})
