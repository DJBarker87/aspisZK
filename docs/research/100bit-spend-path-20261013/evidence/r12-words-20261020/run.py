import os, sys, json, pathlib, subprocess, time, hashlib, re
ROOT=pathlib.Path(__file__).resolve().parents[5]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
E=BASE/'evidence/r12-words-20261020'
OBJ=pathlib.Path('/tmp/cx-r12-words-objects'); OBJ.mkdir(exist_ok=True)
seed=json.loads((BASE/'evidence/sampler-rows-25-32-20261020/frames-v4/command.json').read_text())
paths=[str(OBJ),'/tmp/r1-commit-model-20261019-objects','/tmp/codex-cx-ckpt-log-20261020-objects','/tmp/codex-cx-sampler-20261020-objects','/tmp/cx-wire-tx2-objects','/tmp/codex-cx-stage2b-20261020-objects']+seed['env']['LEAN_PATH'].split(':')[1:]
extra=json.loads((BASE/'evidence/bin-commitment-model-20261019/BinThreeCommitmentTypedOpening/receipt.json').read_text())['lean_path'].split(':')
paths += ['/tmp/root-source-global-oracle-nuc-v1-fetched-20261019/attempt/objects']+extra
paths += ['/tmp/cx-record-classes-objects']+(BASE/'evidence/wire-tx2-20261020/lean-path.txt').read_text().strip().split(':')
paths=list(dict.fromkeys(paths))
env=dict(os.environ,LEAN_PATH=':'.join(paths))
mod,attempt=sys.argv[1:]; src=BASE/'lean'/f'{mod}.lean'; out=E/attempt; out.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports={}
for dep in re.findall(r'^import (\S+)',src.read_text(),re.M):
 for path in paths:
  f=pathlib.Path(path)/(dep.replace('.','/')+'.olean')
  if f.exists(): imports[dep]={'path':str(f),'sha256':sha(f),'size':f.stat().st_size}; break
 else: imports[dep]={'missing':True}
argv=[seed['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(BASE/'lean'),'-o',str(OBJ/f'{mod}.olean'),str(src)]
rec={'module':mod,'attempt':attempt,'argv':argv,'env':{'LEAN_PATH':env['LEAN_PATH']},'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source_sha256':sha(src),'imports':imports}
rec['deps_fingerprint']=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
(out/'command.json').write_text(json.dumps(rec,indent=2)+'\n')
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
 try: lock.mkdir(); break
 except FileExistsError: time.sleep(15)
try:
 while any(len(p)>2 and pathlib.Path(p[1]).name=='lean' and '-M4400' in p[2] for p in (x.split(None,2) for x in subprocess.check_output(['ps','-axo','pid,comm,args'],text=True).splitlines())): time.sleep(15)
 t=time.monotonic()
 with (out/'stdout.log').open('w') as so,(out/'time.log').open('w') as se:
  r=subprocess.run(['/usr/bin/time','-l']+argv,env=env,cwd=ROOT,stdout=so,stderr=se)
 rec.update(exit=r.returncode,wall_seconds=time.monotonic()-t)
finally: lock.rmdir()
timing=(out/'time.log').read_text(); output=(out/'stdout.log').read_text()
rec['peak_rss_bytes']=int(re.search(r'(\d+)\s+maximum resident set size',timing).group(1))
rec['swaps']=int(re.search(r'(\d+)\s+swaps',timing).group(1))
rec['axioms']=re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*?(?=\n[^ ]|\Z)",output,re.M|re.S)
(out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:rec[k] for k in ['module','exit','wall_seconds','peak_rss_bytes','swaps']}),flush=True)
print(output,flush=True)
sys.exit(r.returncode)
