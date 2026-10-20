#!/usr/bin/env python3
"""One-module focused local checker; private objects and shared mkdir lock."""
import hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[5]
E=Path(__file__).resolve().parent
OBJ=Path('/tmp/codex-cx-bindings-20261020-objects');OBJ.mkdir(exist_ok=True)
LEAN=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
old=json.loads((ROOT/'docs/research/100bit-spend-path-20261013/evidence/rr-total-normalization-query-cost-20261019/RRConcreteRawStateValidity/command.json').read_text())['environment']['LEAN_PATH']
LP=str(OBJ)+':/tmp/root-finish-prefix-deps-20261018:/tmp/g3-missing-mac-incoming-20261018/objects:'+old
module,rel=sys.argv[1:3];src=ROOT/rel; target=OBJ/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=E/(module+"-"+(sys.argv[3] if len(sys.argv)>3 else sha(src)[:12])); a.mkdir(exist_ok=False)
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try: lock.mkdir();break
 except FileExistsError: time.sleep(15)
try:
 while True:
  ps=subprocess.check_output(['ps','-axo','comm=,args='],text=True)
  if not any(re.match(r'\S*lean\s',l.strip()) and '-M4400' in l for l in ps.splitlines()):break
  time.sleep(60)
 argv=['/usr/bin/time','-l',str(LEAN),'-j1','-M4400','-DElab.async=false','-R',str(src.parent if '.' not in module else src.parents[len(module.split('.'))-1]),'-o',str(target),str(src)]
 (a/'command.json').write_text(json.dumps(dict(argv=argv,environment=dict(LEAN_PATH=LP)),indent=2)+'\n')
 start=time.monotonic()
 with (a/'output.log').open('w') as out,(a/'time.log').open('w') as err:
  p=subprocess.run(argv,env=dict(os.environ,LEAN_PATH=LP),stdout=out,stderr=err)
 wall=time.monotonic()-start
finally:lock.rmdir()
log=(a/'output.log').read_text();tl=(a/'time.log').read_text()
imports=[]
for dep in re.findall(r'^import (\S+)',src.read_text(),re.M):
 for d in LP.split(':'):
  q=Path(d)/(dep.replace('.','/')+'.olean')
  if q.is_file():imports.append(dict(module=dep,path=str(q),sha256=sha(q),size=q.stat().st_size));break
reports=re.findall(r"(?:'[^']+' (?:depends on axioms:|does not depend on any axioms)\s*(?:\[[^\]]*\])?)",log,re.S)
rss=re.search(r'(\d+)\s+maximum resident set size',tl);swaps=re.search(r'(\d+)\s+swaps',tl)
receipt=dict(module=module,source=rel,source_sha256=sha(src),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),exit_status=p.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(swaps[1]) if swaps else None,axiom_reports=reports,imports=imports)
if p.returncode==0:receipt.update(object_sha256=sha(target),object_size=target.stat().st_size)
(a/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(log); print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
