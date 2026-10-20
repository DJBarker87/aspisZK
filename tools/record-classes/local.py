import pathlib, json, os, hashlib, subprocess, time, re, sys
base=pathlib.Path('docs/research/100bit-spend-path-20261013')
root=pathlib.Path.cwd()
ev=base/'evidence/record-classes-20261019'; ev.mkdir(exist_ok=True)
obj=pathlib.Path('/tmp/cx-record-classes-objects'); obj.mkdir(exist_ok=True)
old=json.loads((base/'evidence/bin-commitment-model-20261019/BinGrammar/receipt.json').read_text())
paths=[str(obj),'/tmp/cx-wire-len-objects','/tmp/r1-commit-model-20261019-objects']+old['lean_path'].split(':')
leanpath=':'.join(dict.fromkeys(paths))
for mod in sys.argv[1:] or ['WireBindingRecordCodec','BinWireBindingLengths']:
 d=ev/mod; d.mkdir(exist_ok=True)
 src=root/base/'lean'/f'{mod}.lean'
 sha=hashlib.sha256(src.read_bytes()).hexdigest()
 deps=[]
 for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
  for path in paths:
   f=pathlib.Path(path)/(imp.replace('.','/')+'.olean')
   if f.exists():
    deps.append({'module':imp,'object_path':str(f),'object_sha256':hashlib.sha256(f.read_bytes()).hexdigest()}); break
 fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
 if any(hashlib.sha256(json.dumps(json.loads(f.read_text()).get('direct_imports'),sort_keys=True).encode()).hexdigest() == fp and json.loads(f.read_text()).get('exit_status') == 0 and json.loads(f.read_text()).get('source_sha256') == sha for f in d.glob('attempt-*/receipt.json')):
  print(mod, 'already green for this source and dependencies; no unchanged rerun', flush=True); continue
 attempt=d/f'attempt-{sha[:12]}-{hashlib.sha256(leanpath.encode()).hexdigest()[:6]}';
 n=1
 while attempt.exists():
  attempt=d/f'attempt-{sha[:12]}-{hashlib.sha256(leanpath.encode()).hexdigest()[:6]}-{n}'; n+=1
 attempt.mkdir()
 (attempt/'source.lean').write_bytes(src.read_bytes())
 cmd=[old['command'][2],'-j1','-M4400','-DElab.async=false','-o',str(obj/f'{mod}.olean'),str(src)]
 lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
 while True:
  try: lock.mkdir(); break
  except FileExistsError: time.sleep(15)
 try:
  while any(x.split() and x.split()[0].endswith('/lean') and '-M4400' in x for x in subprocess.check_output(['ps','-axo','args='],text=True).splitlines()): time.sleep(60)
  env=os.environ|{'LEAN_PATH':leanpath}
  t=time.monotonic()
  with (attempt/'lean.log').open('w') as out, (attempt/'time.log').open('w') as err:
   p=subprocess.run(['/usr/bin/time','-l']+cmd,env=env,stdout=out,stderr=err)
  wall=time.monotonic()-t
 finally: lock.rmdir()
 log=(attempt/'lean.log').read_text(); tl=(attempt/'time.log').read_text()
 imports=[]
 for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
  for path in paths:
   f=pathlib.Path(path)/(imp.replace('.','/')+'.olean')
   if f.exists():
    imports.append({'module':imp,'object_path':str(f),'object_sha256':hashlib.sha256(f.read_bytes()).hexdigest()});break
 rec={'module':mod,'source':str(src.relative_to(root)),'source_sha256':sha,'exit_status':p.returncode,'wall_seconds':wall,'peak_rss_bytes':int(re.search(r'(\d+)\s+maximum resident set size',tl)[1]),'process_swap_count':int(re.search(r'(\d+)\s+swaps',tl)[1]),'source_revision_parent':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'command':cmd,'lean_path':leanpath,'direct_imports':imports,'deps_fingerprint':fp,'axioms':re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S),'errors':[x for x in log.splitlines() if 'error:' in x]}
 if p.returncode == 0:
  output=obj/f'{mod}.olean'
  rec.update(object_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),object_size_bytes=output.stat().st_size)
 (attempt/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(mod,p.returncode,log,flush=True)
 manifest={'schema':'focused-extractor-proof-packet-v1','attempts':[json.loads(f.read_text()) for f in ev.glob('*/attempt-*/receipt.json')]}
 (ev/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 if p.returncode: break
