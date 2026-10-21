#!/usr/bin/env python3
"""Single focused local module, prescribed mkdir lock and -M4400 limit."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s7-kani-20261021/proofs'/sys.argv[1]
module=sys.argv[2];source=B/'lean'/(module.replace('.', '/')+'.lean');E.mkdir(parents=True,exist_ok=False)
ref=json.loads((B/'evidence/transfer-bindings-20261020/ExtractedAdapterTransferBindings/command.json').read_text())
objects=Path('/tmp/codex-cx-s7-kani-20261021-objects');objects.mkdir(exist_ok=True)
env=dict(os.environ);env['LEAN_PATH']=str(objects)+':/tmp/r1-circle-pointwise-coalesced-local-v1/objects:/tmp/cx-geometry-20261020-objects:'+ ':/tmp/codex-cx-r20-pool-handoff-20261020-objects:/tmp/root-finish-prefix-deps-20261018:'+ref['environment']['LEAN_PATH']
compiler='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
(objects/(module.replace('.', '/')+'.olean')).parent.mkdir(parents=True,exist_ok=True)
cmd=[compiler,'-j1','-M4400','-DElab.async=false','-o',str(objects/(module.replace('.', '/')+'.olean')),str(source)]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
lock=Path('/tmp/aspis-local-lean.lock.d');start=time.monotonic()
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 while True:
  active=[l for l in subprocess.check_output(['ps','-axo','pid=,args='],text=True).splitlines() if len(l.split())>1 and Path(l.split()[1]).name == 'lean' and '-M4400' in l]
  if not active:break
  time.sleep(60)
 imports={}
 for name in re.findall(r'^import ([A-Za-z0-9_.]+)',source.read_text(),re.M):
  for d in env['LEAN_PATH'].split(':'):
   q=Path(d)/(name.replace('.', '/')+'.olean')
   if q.exists():imports[name]=dict(object_path=str(q),sha256=sha(q));break
  assert name in imports, name
 meta=dict(direct_imports=imports,schema='focused-extractor-proof-packet-v1',module=module,command=cmd,source_sha256=sha(source),source_revision=subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip(),compiler_sha256=sha(compiler),lean_path=env['LEAN_PATH'])
 (E/'source.lean').write_bytes(source.read_bytes())
 (E/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
 with (E/'lean.log').open('w') as log,(E/'time.log').open('w') as timing:
  t=time.monotonic();p=subprocess.run(['/usr/bin/time','-l',*cmd],cwd=source.parent,env=env,stdout=log,stderr=timing);wall=time.monotonic()-t
 log=(E/'lean.log').read_text();timing=(E/'time.log').read_text()
 rss=re.search(r'(\d+)\s+maximum resident set size',timing)
 rec=dict(**meta,exit_status=p.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(re.search(r'(\d+)\s+swaps',timing)[1]),print_axioms=re.findall(r"'[^\n]+' (?:depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",log))
 rec['deps_fingerprint']=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
 (E/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));print(log);raise SystemExit(p.returncode)
finally:
 try:lock.rmdir()
 except FileNotFoundError:print("Lock directory was externally removed before cleanup",file=sys.stderr)
