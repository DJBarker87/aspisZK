"""Read-only host recovery; never submits a proof job."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';D='/home/dombarker/project-offloads/codex-pv-kstub-20261028'
code="""from pathlib import Path
import json
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028')
print(json.dumps({str(p.relative_to(D)):p.read_text() for d in sorted(D.glob('K[0-9][0-9]')) for p in d.iterdir() if p.is_file()}))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True)
files=json.loads(r.stdout);manifest=[]
for rel,data in files.items():
 p=E/rel;p.parent.mkdir(exist_ok=True)
 # Retain local retry histories, which are collected by the Mac wrapper.
 if p.exists() and p.read_text()!=data:
  manifest.append(dict(path=rel,local_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),host_sha256=hashlib.sha256(data.encode()).hexdigest(),action='retained local; saved host snapshot'))
  p=p.with_name(p.name+'.host-recovery.txt')
 p.write_text(data)
(E/'recovery-host-files.json').write_text(json.dumps(manifest,indent=2)+'\n')
name='K16';out=E/name;tim=(out/'time.log').read_text()
def field(s):
 m=re.search(s+r':\s*(.+)',tim);return m[1] if m else None
previous=json.loads((E/'K15/receipt.json').read_text());target=json.loads((E/(name+'-target.json')).read_text())
receipt=dict(previous,target=[x.replace('/K15/','/K16/') for x in previous['target'][:20]]+target['command'],exit=int(field('Exit status')),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),recovered_read_only=True,source_revision='03984c6b6e123cc9d7283900e518627ade9c6b49')
# Derive exact wrapper prefix from prior receipt rather than assuming argument count.
prefix=previous['target'][:previous['target'].index('timeout')]
receipt['target']=[x.replace('/K15/','/K16/') for x in prefix]+target['command']
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
result={k:v for k,v in target.items() if k not in ['command','negative_control']}
result.update(run=name,negative_control=False,status='TIMEOUT',receipt=str((out/'receipt.json').relative_to(R)))
(E/(name+'-result.json')).write_text(json.dumps(result,indent=2)+'\n')
print('Recovered K16: exit',receipt['exit'],'wall',receipt['wall'],'without running Kani')
