#!/usr/bin/env python3
"""One local Lean module, private objects, mkdir admission and resource receipt."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys,time
root=Path.cwd(); packet=root/'docs/research/100bit-spend-path-20261013/evidence/repin-s2-20261020'
source=root/sys.argv[1]; attempt=sys.argv[2]
receipt=packet/attempt;receipt.mkdir(exist_ok=False)
base=json.loads((root/'docs/research/100bit-spend-path-20261013/evidence/overflow-freedom-20261019/receipts/AspisR1DecodeKFullV10.Funs-20261020T073930.249643Z/command.json').read_text())
obj=Path('/tmp/codex-cx-repin-s2-20261020-objects');obj.mkdir(exist_ok=True)
paths=[str(obj),'/tmp/root-finish-prefix-deps-20261018','/tmp/g3-missing-mac-incoming-20261018/objects']+base['lean_path'].split(':')
paths=list(dict.fromkeys(paths)); env=dict(os.environ,LEAN_PATH=':'.join(paths))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
imports=[]
for module in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
 p=next((Path(d)/(module.replace('.','/')+'.olean') for d in paths if (Path(d)/(module.replace('.','/')+'.olean')).exists()),None)
 assert p,module
 imports.append(dict(module=module,object=str(p),sha256=sha(p)))
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 while True:
  procs=subprocess.run(['pgrep','-fl','lean'],text=True,capture_output=True).stdout
  running=[s for s in procs.splitlines() if '-M4400' in s and re.search(r'/bin/lean(?: |$)',s)]
  if not running:break
  time.sleep(60)
 compiler='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
 cmd=['/usr/bin/time','-l',compiler,'-j1','-M4400','-DElab.async=false','-o',str(obj/(source.stem+'.olean')),str(source)]
 rec=dict(schema='focused-extractor-proof-packet-v1',module=source.stem,source=str(source.relative_to(root)),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=sha(source),command=cmd,lean_path=env['LEAN_PATH'],imports=imports,compiler_sha256=sha(compiler),admission_rule='mkdir lock plus no other -M4400 Lean process',started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 start=time.monotonic()
 with (receipt/'out.log').open('w') as out,(receipt/'time.log').open('w') as err:
  run=subprocess.run(cmd,env=env,stdout=out,stderr=err)
 rec.update(exit=run.returncode,wall_s=time.monotonic()-start)
 t=(receipt/'time.log').read_text(); o=(receipt/'out.log').read_text()
 m=re.search(r'(\d+)\s+maximum resident set size',t);rec['peak_rss_bytes']=int(m[1]) if m else None
 m=re.search(r'(\d+)\s+swaps',t);rec['process_swaps']=int(m[1]) if m else None
 rec['axioms']=re.findall(r"(?:'[^'\n]+' (?:depends on axioms: \[[^]]*\]|does not depend on any axioms))",o,re.S)
 rec['deps_fingerprint']=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
 (receipt/'command.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps(rec,indent=2));print(o);sys.exit(run.returncode)
finally:lock.rmdir()
