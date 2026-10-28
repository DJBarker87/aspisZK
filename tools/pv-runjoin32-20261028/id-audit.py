from pathlib import Path
import subprocess,shlex,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028'
code=r'''import pathlib,os,re,json
root=pathlib.Path('/home/dombarker/project-offloads');hits=[];pat=re.compile(r'(?<!\d)(51[34]\d\d)(?!\d)')
for job in root.glob('codex-pv-*'):
 for base in [job/'evidence']:
  if not base.is_dir():continue
  for path,ds,fs in os.walk(base):
   if len(pathlib.Path(path).relative_to(base).parts)>4:ds[:]=[];continue
   for f in fs:
    ids=[int(m[1]) for m in pat.finditer(f) if 51300<=int(m[1])<=51499]
    if ids:hits.append(dict(path=str(pathlib.Path(path)/f),ids=ids))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[s for s in sent.read_text().splitlines() if len(s.split())>=3 and s.split()[2].isdigit() and 51300<=int(s.split()[2])<=51499]
print(json.dumps(dict(block=[51300,51499],receipt_hits=hits,sent_hits=lines)))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'id-block-audit.json').write_text(json.dumps(x,indent=2)+'\n');print(x);assert not x['receipt_hits'] and not x['sent_hits']
