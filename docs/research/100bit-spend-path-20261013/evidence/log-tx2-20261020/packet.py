#!/usr/bin/env python3
"""Focused local Lean runner and receipt checker; no shared objects are written."""
import hashlib,json,os,pathlib,re,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[5]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
PACK=pathlib.Path(__file__).resolve().parent
OBJ=pathlib.Path('/tmp/codex-cx-log-tx2-20261020-objects')
LEAN='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def paths():
 a=json.loads((BASE/'evidence/checkpoint-log-tx1-20261020/log-v1/command.json').read_text())['environment']['LEAN_PATH']
 b=json.loads((BASE/'evidence/stage2-continuation-20261020/proofs/resume-fact-v4/command.json').read_text())['lean_path']
 return list(dict.fromkeys([str(OBJ),'/tmp/codex-cx-ckpt-log-20261020-objects','/tmp/codex-cx-stage2b-20261020-objects']+a.split(':')+b.split(':')))
def imports(src,ps):
 found={}
 def walk(mod):
  if mod in found:return
  rel=mod.replace('.','/')+'.olean'
  f=next((pathlib.Path(p)/rel for p in ps if (pathlib.Path(p)/rel).is_file()),None)
  if f is None:raise RuntimeError('missing import '+mod)
  found[mod]={'path':str(f),'sha256':sha(f),'size':f.stat().st_size}
 for mod in re.findall(r'^import\s+(\S+)',src,re.M):walk(mod)
 return found
if len(sys.argv)>1:
 mod,attempt=sys.argv[1:];src=BASE/'lean'/f'{mod}.lean'; ps=paths(); deps=imports(src.read_text(),ps)
 fingerprint=hashlib.sha256(json.dumps({'imports':deps,'lean_path':ps},sort_keys=True).encode()).hexdigest()
 for previous in PACK.glob('*/receipt.json'):
  old=json.loads(previous.read_text()); oldcmd=json.loads((previous.parent/'command.json').read_text())
  assert not (old['source_sha256']==sha(src) and oldcmd['imports']==deps and oldcmd['environment']['LEAN_PATH']==':'.join(ps)), 'Refused unchanged source/dependencies/environment'
 out=PACK/attempt;out.mkdir();OBJ.mkdir(exist_ok=True)
 argv=[LEAN,'-j1','-M4400','-DElab.async=false','-o',str(OBJ/f'{mod}.olean'),str(src)]
 cmd={'argv':['/usr/bin/time','-l']+argv,'environment':{'LEAN_PATH':':'.join(ps)},'imports':deps}
 (out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
 lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
 while True:
  try:lock.mkdir();break
  except FileExistsError:time.sleep(15)
 try:
  # Exact executable-name match avoids matching shell command strings.
  while subprocess.run(['pgrep','-x','lean'],stdout=subprocess.DEVNULL).returncode==0:time.sleep(15)
  env=os.environ.copy();env['LEAN_PATH']=':'.join(ps)
  with (out/'lean.log').open('w') as log,(out/'time.log').open('w') as tm:
   t=time.monotonic();r=subprocess.run(['/usr/bin/time','-l']+argv,env=env,stdout=log,stderr=tm);wall=time.monotonic()-t
 finally:lock.rmdir()
 timing=(out/'time.log').read_text();lines=(out/'lean.log').read_text().splitlines()
 rec={'schema':'focused-extractor-proof-packet-v1','module':mod,'attempt':attempt,'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'working_source_changes':subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True).splitlines(),'exit':r.returncode,'wall_seconds':wall,'peak_rss_bytes':int(re.search(r'(\d+)\s+maximum resident set size',timing)[1]),'swaps':int(re.search(r'(\d+)\s+swaps',timing)[1]),'axiom_lines':re.findall(r"'[^\n]*'(?: depends on axioms: \[.*?\]| does not depend on any axioms)",'\n'.join(lines),re.S),'dependency_fingerprint':hashlib.sha256(json.dumps({'imports':deps,'lean_path':ps},sort_keys=True).encode()).hexdigest(),'command':str((out/'command.json').relative_to(PACK))}
 (out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 receipts=[json.loads(p.read_text()) for p in sorted(PACK.glob('*/receipt.json'))]
 (PACK/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':receipts},indent=2)+'\n')
 print(json.dumps(rec,indent=2));sys.exit(r.returncode)
else:
 for r in json.loads((PACK/'manifest.json').read_text())['attempts']:
  if r['exit']==0:
   assert sha(ROOT/r['source'])==r['source_sha256'],r['module']
   assert len(r['axiom_lines'])==len(re.findall(r'^#print axioms ',(ROOT/r['source']).read_text(),re.M)),r['module']
   names=set()
   for line in r['axiom_lines']:
    match=re.search(r'depends on axioms: \[(.*?)\]',line,re.S)
    if match:names.update(x.strip() for x in match[1].split(','))
   assert names <= {'propext','Classical.choice','Quot.sound'},names
 print('Packet source hashes and successful audits checked.')
