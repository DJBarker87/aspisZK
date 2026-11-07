from pathlib import Path
import subprocess,sys,json,hashlib,lzma,re,time,shutil
B=Path.cwd();mode=sys.argv[1];T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if mode=='link':
 name=sys.argv[2];sources=['NMG_native/'+name+'.c','NMG_native/NFA_WALKER.c','NMG_native/NFA_MemoryLimit.c']
 r=subprocess.run([T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMG_native/'+name,*sources]);assert r.returncode==0
 p=B/'NMG_native'/name;(B/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,sources={n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in sources})))
 print(name+' optimized link exit0');sys.exit(0)
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
