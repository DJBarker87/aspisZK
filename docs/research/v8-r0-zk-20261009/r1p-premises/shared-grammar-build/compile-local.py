import hashlib,json,os,pathlib,re,subprocess,sys,time
repo=pathlib.Path.cwd(); base=repo/'docs/research/100bit-spend-path-20261013'; ev=base/'evidence/shared-grammar-20261020'; ev.mkdir(parents=True,exist_ok=True)
obj=pathlib.Path('/tmp/cx-shared-grammar-objects'); obj.mkdir(exist_ok=True)
old=json.loads((base/'evidence/record-classes-20261019/manifest.json').read_text())['attempts'][0]
lp=str(obj)+':'+old['lean_path']; mod=sys.argv[1]; src=base/'lean'/f'{mod}.lean'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
imports=[]
for m in re.findall(r'^import (\S+)',src.read_text(),re.M):
 p=next((pathlib.Path(d)/(m.replace('.','/')+'.olean') for d in lp.split(':') if (pathlib.Path(d)/(m.replace('.','/')+'.olean')).exists()),None)
 if p is None: raise RuntimeError('missing import '+m)
 imports.append({'module':m,'object_path':str(p),'object_sha256':sha(p)})
fp=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest(); key=sha(src)[:12]+'-'+fp[:8]; dest=ev/mod/key; dest.mkdir(parents=True,exist_ok=True)
if (dest/'receipt.json').exists(): raise RuntimeError('unchanged input')
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
 try: lock.mkdir(); break
 except FileExistsError: time.sleep(15)
try:
 while True:
  ps=subprocess.run(['ps','-axo','command='],text=True,capture_output=True).stdout
  if not any(l.split()[0].endswith('/lean') and '-M4400' in l for l in ps.splitlines() if l.split()): break
  time.sleep(60)
 argv=[str(pathlib.Path.home()/'.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),'-j1','-M4400','-DElab.async=false','-R',str(base/'lean'),'-o',str(obj/f'{mod}.olean'),str(src)]
 env=dict(os.environ,LEAN_PATH=lp); start=time.monotonic()
 with (dest/'lean.log').open('w') as out,(dest/'time.log').open('w') as tl:
  p=subprocess.run(['/usr/bin/time','-l']+argv,env=env,stdout=out,stderr=tl)
 wall=time.monotonic()-start
finally: lock.rmdir()
out=(dest/'lean.log').read_text(); tl=(dest/'time.log').read_text()
get=lambda pat:int(re.search(pat,tl).group(1)) if re.search(pat,tl) else None
r={'module':mod,'source':str(src.relative_to(repo)),'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'exit_status':p.returncode,'wall_seconds':wall,'peak_rss_bytes':get(r'(\d+)\s+maximum resident set size'),'process_swap_count':get(r'(\d+)\s+swaps'),'command':argv,'lean_path':lp,'direct_imports':imports,'deps_fingerprint':fp,'axioms':re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out),'errors':[l for l in out.splitlines() if 'error:' in l]}
(dest/'receipt.json').write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps(r,indent=2)[:1100]); print(out)
manifest=ev/'manifest.json'; data=json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}; data['attempts'].append(r); manifest.write_text(json.dumps(data,indent=2)+'\n')
sys.exit(p.returncode)
