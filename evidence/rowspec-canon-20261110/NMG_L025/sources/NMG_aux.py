from pathlib import Path
import subprocess,sys,json,hashlib,lzma,re,time,shutil
B=Path.cwd();mode=sys.argv[1];T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if mode=='link':
 name=sys.argv[2];sources=['NMG_native/'+name+'.c','NMG_native/NFA_WALKER.c','NMG_native/NFA_MemoryLimit.c']
 r=subprocess.run([T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMG_native/'+name,*sources]);assert r.returncode==0
 p=B/'NMG_native'/name;(B/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,sources={n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in sources})))
 print(name+' optimized link exit0');sys.exit(0)
if mode=='proof0':
 rows=[json.loads(l) for l in (B/'NMG_LOADED_scan.jsonl').read_text().splitlines()]
 roots=__import__('os').environ['LEAN_PATH'].split(':');pins=[]
 for row in rows:
  rel=row['module'].replace('.','/')+'.olean'
  p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
  assert p is not None,rel
  for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if z.is_file():pins.append(dict(module=row['module'],path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size))
 data=json.dumps(dict(selected_objects=pins,LEAN_PATH=roots,modules=len(rows))).encode();(B/'NMG_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(data,preset=1));(B/'NMG_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
 export=B/'NMG_exports_20261110';export.mkdir(exist_ok=True);exported=[]
 for p in (B/'NMG_objects').iterdir():
  if p.is_file() and p.name.startswith('NMG_') and any(p.name.endswith(x) for x in ['.olean','.olean.private','.olean.server','.ir']):
   q=export/p.name;shutil.copy2(p,q);exported.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 (B/'NMG_EXPORT.json').write_text(json.dumps(dict(path=str(export),files=exported,disk=shutil.disk_usage(B)._asdict(),own_bytes=int(subprocess.check_output(['du','-sb',str(B)]).split()[0]))))

folder=B/'NMG_audit'/mode;folder.mkdir(parents=True,exist_ok=True)
if mode=='scan':cmd=['NMG_native/NMG_Driver','scan']
else:cmd=['NMG_native/NMG_ProofDriver',mode]
pin=B/('NMG_Driver_BINARY_PIN.json' if mode=='scan' else 'NMG_ProofDriver_BINARY_PIN.json');assert hashlib.sha256((B/cmd[0]).read_bytes()).hexdigest()==json.loads(pin.read_text())['sha256']
start=time.monotonic()
with (folder/'stdout.log').open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
raw=(folder/'stdout.log').read_text();results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')]
manifest=[]
for p in list(B.glob('NEP_'+mode+'_*_REACHABLE.txt'))+[folder/'stdout.log']:
 data=p.read_bytes();dest=folder/(p.name+'.xz');dest.write_bytes(lzma.compress(data,preset=1));(folder/(p.name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'\n');manifest.append(dict(path=str(dest.relative_to(B)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)));p.unlink()
if mode=='scan':
 p=B/'NMG_LOADED_scan.jsonl';shutil.copy2(p,folder/p.name)
 scan=[json.loads(l) for l in p.read_text().splitlines()];good=r.returncode==0 and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
else:
 expected=json.loads((B/'NMG_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])] if mode!='fixtures' else None
 assert expected is None or set(expected)=={x['root'] for x in results}
 good=all(set(x['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'} for x in results) if mode!='fixtures' else r.returncode==0 and len(results)==8 and all(x['equal'] for x in results)
receipt=dict(mode=mode,command=cmd,binary_pin=json.loads(pin.read_text()),exit_status=r.returncode,wall_seconds=time.monotonic()-start,results=results,raw_standard_only=good,archives=manifest)
(folder/'result.json').write_text(json.dumps(receipt,indent=1));print(json.dumps(dict(mode=mode,exit_status=r.returncode,roots=len(results),standard_only=good)))
sys.exit(r.returncode)
