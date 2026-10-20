import pathlib,json,os,subprocess,time,hashlib,re,sys
root=pathlib.Path.cwd(); base=root/'docs/research/100bit-spend-path-20261013'; evidence=base/'evidence/qv-stage2-20261020'
old=json.loads((base/'evidence/qv-stage1-20261020/manifest.json').read_text())['attempts'][-1]
obj=pathlib.Path('/tmp/cx-qv-stage2-objects');obj.mkdir(exist_ok=True)
paths=[str(obj),'/tmp/cx-qv-stage1-objects','/tmp/cx-record-classes-objects','/tmp/cx-wire-tx2-objects','/tmp/codex-cx-stage2b-20261020-objects']+old['lean_path'].split(':')+['/tmp/aspis-root-local-semantic-20261015/objects']
lean='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
source=root/sys.argv[1]; module=sys.argv[2] if len(sys.argv)>2 else source.stem
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 while True:
  running=subprocess.run(['pgrep','-fl','/bin/lean.*-M4400'],capture_output=True,text=True).stdout
  if not running.strip():break
  time.sleep(60)
 manifest=evidence/'manifest.json';data=json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
 n=len(data['attempts'])+1
 cmd=[lean,'-j1','-M4400','-DElab.async=false','-o',str(obj/(module+'.olean')),str(source)]
 imports=[]
 for name in re.findall(r'^import (\S+)',source.read_text(),re.M):
  path=next((pathlib.Path(p)/(name.replace('.','/')+'.olean') for p in paths if (pathlib.Path(p)/(name.replace('.','/')+'.olean')).exists()),None)
  imports.append({'module':name,'object_path':str(path),'object_sha256':hashlib.sha256(path.read_bytes()).hexdigest() if path else None})
 key=(hashlib.sha256(source.read_bytes()).hexdigest(), hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest())
 if any((r['source_sha256'],r['deps_fingerprint'])==key for r in data['attempts']):raise RuntimeError('unchanged source/dependencies already attempted')
 t=time.monotonic()
 proc=subprocess.run(['/usr/bin/time','-l']+cmd,env={**os.environ,'LEAN_PATH':':'.join(paths)},capture_output=True,text=True)
 wall=time.monotonic()-t
 (evidence/f'out-{n}.log').write_text(proc.stdout);(evidence/f'time-{n}.log').write_text(proc.stderr)
 rss=re.search(r'(\d+)\s+maximum resident set size',proc.stderr);swaps=re.search(r'(\d+)\s+swaps',proc.stderr)
 receipt={'module':module,'source':str(source.relative_to(root)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'source_revision_parent':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'command':cmd,'lean_path':':'.join(paths),'direct_imports':imports,'deps_fingerprint':hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest(),'exit_status':proc.returncode,'wall_seconds':wall,'peak_rss_bytes':int(rss[1]) if rss else None,'process_swap_count':int(swaps[1]) if swaps else None,'axioms_output':proc.stdout,'errors':proc.stderr.split('real')[0] if proc.returncode else ''}
 data['attempts'].append(receipt);manifest.write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({k:receipt[k] for k in ['module','exit_status','wall_seconds','peak_rss_bytes','process_swap_count']}));print(proc.stdout);print(proc.stderr if proc.returncode else '')
finally:lock.rmdir()
