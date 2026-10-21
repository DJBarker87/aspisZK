#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
module=sys.argv[1];attempt=sys.argv[2]
src=B/'lean-candidates/s126-caller-boundary-20261021'/(module+'.lean')
E=B/'evidence/s126-current-caller-20261021'/attempt;E.mkdir(parents=True,exist_ok=False)
objects=Path('/tmp/s126-current-caller-20261021-objects');objects.mkdir(exist_ok=True)
ref=json.loads((B/'evidence/repin-s6-20261020/proofs/first-v2/command.json').read_text())
env=dict(os.environ);env['LEAN_PATH']=str(objects)+':'+ref['lean_path']
if len(sys.argv)>3:env['LEAN_PATH']=str(objects)+':'+sys.argv[3]+':/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'
lock=Path('/tmp/aspis-local-lean.lock.d')
waitstart=time.monotonic()
while True:
 try:lock.mkdir();break
 except FileExistsError:
  if time.monotonic()-waitstart>240:
   (E/'preflight.json').write_text(json.dumps(dict(status='not_launched',reason='local Lean lock retained'))+'\n')
   raise SystemExit('Existing local Lean lock retained; no compiler launched.')
  time.sleep(0.5)
try:
 (lock/'owner.json').write_text(json.dumps(dict(pid=os.getpid(),branch='codex/s126-caller-20261021',target=module)))
 lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
 lake=lean.with_name('lake')
 cmd=[str(lake),'env','/usr/bin/env','LEAN_PATH='+env['LEAN_PATH'],str(lean),'-j1','-M4400','-R',str(src.parent),'-o',str(objects/(module+'.olean')),str(src)]
 sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
 imports={}
 for name in re.findall(r'^import ([A-Za-z0-9_.]+)',src.read_text(),re.M):
  for d in env['LEAN_PATH'].split(':'):
   p=Path(d)/(name.replace('.','/')+'.olean')
   if p.exists():imports[name]=dict(path=str(p),sha256=sha(p));break
  assert name in imports,name
 meta=dict(schema='focused-extractor-proof-packet-v1',target=module,command=cmd,cwd='/Users/dominic/ZK/AspisFormal',source_revision=subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip(),source_sha256=sha(src),tool_pins={str(p):sha(p) for p in [lean,lake]},direct_imports=imports,lean_path=env['LEAN_PATH'])
 (E/'source.lean').write_bytes(src.read_bytes());(E/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
 start=time.monotonic()
 with (E/'lean.log').open('w') as log,(E/'time.log').open('w') as timing:
  p=subprocess.run(['/usr/bin/time','-l',*cmd],cwd=meta['cwd'],env=env,stdout=log,stderr=timing)
 wall=time.monotonic()-start;tl=(E/'time.log').read_text();log=(E/'lean.log').read_text()
 def metric(m):
  x=re.search(r'(\d+)\s+'+m,tl);return int(x[1]) if x else None
 audits=re.findall(r"'[^\n]+' (?:depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",log)
 rec=dict(**meta,exit_status=p.returncode,wall_seconds=wall,peak_rss_bytes=metric('maximum resident set size'),swaps=metric('swaps'),print_axioms=audits)
 if p.returncode==0:rec['object_sha256']=sha(objects/(module+'.olean'))
 (E/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps({k:rec[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']}));print(log[:3000]);raise SystemExit(p.returncode)
finally:
 (lock/'owner.json').unlink();lock.rmdir()
