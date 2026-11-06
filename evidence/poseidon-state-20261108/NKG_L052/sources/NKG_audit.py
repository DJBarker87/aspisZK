from pathlib import Path
import subprocess,json,sys,hashlib,lzma
B=Path(__file__).resolve().parent;mode,a=sys.argv[1:];out=B/(a+'_validation');out.mkdir(exist_ok=False)
config=json.loads((B/(a+'.json')).read_text())
for name,info in config['deps_fingerprint']['audit_inputs'].items():assert hashlib.sha256((B/name).read_bytes()).hexdigest()==info['sha256'],name
binary=B/'NKG_native'/('NKG_Driver'if mode=='scan'else'NKG_ProofDriver')
with(out/'audit.log').open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'audit.time'),str(binary),mode],cwd=B,stdout=f,stderr=subprocess.STDOUT)
raw=(out/'audit.log').read_text();rows=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')]
(out/'NKG_RESULTS.json').write_text(json.dumps(dict(mode=mode,exit_status=r.returncode,results=rows,binary=dict(path=str(binary),sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size)),indent=2)+'\n')
# Retain all raw reachability inputs once as compressed evidence and original SHA.
for p in B.glob('NEP_'+mode+'_*_REACHABLE.txt'):
 data=p.read_bytes();(out/('NKG_'+p.name+'.xz')).write_bytes(lzma.compress(data,preset=6));(out/('NKG_'+p.name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'\n')
print(json.dumps(dict(mode=mode,exit_status=r.returncode,roots=len(rows),binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest())))
sys.exit(r.returncode)
