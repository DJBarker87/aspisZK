from pathlib import Path
import subprocess,json,shlex,datetime,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin69-20261101'
code=r'''import pathlib,re,json,time,subprocess
root=pathlib.Path('/home/dombarker/project-offloads');p=root/'codex-pv-runjoin-20261026/runjoin32-lean';pat=re.compile(r'(^|[-_])(?:7809[1-6]|794\d\d)([-_.]|$)');hits=[]
for job in root.glob('codex-pv-*'):
 for base in [job/'evidence',job/'runjoin32-lean/evidence']:
  if base.exists():
   for q in base.rglob('*'):
    if q.is_file() and pat.search(q.name):hits.append(str(q))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if re.search(r'\b(?:7809[1-6]|794\d\d)\b',l)]
print(json.dumps(dict(epoch=time.time(),host_hits=hits,sent_hits=lines)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True,check=True)
x=json.loads(r.stdout);x['local_hits']=[str(p) for p in (R/'evidence').rglob('*') if p.is_file() and re.search(r'(^|[-_])(?:7809[1-6]|794\d\d)([-_.]|$)',p.name)];x['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(E/'new-block-scan.json').write_text(json.dumps(x,indent=2)+'\n');assert not x['host_hits'] and not x['sent_hits'] and not x['local_hits'];print('Assigned leftovers and 79400–79499 empty on host, sent table and local evidence')
