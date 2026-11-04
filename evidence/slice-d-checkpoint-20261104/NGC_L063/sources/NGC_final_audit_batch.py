from pathlib import Path
import subprocess,json,hashlib,lzma,sys,time,os
b=Path.cwd();out=b/'NGC_final_audit';out.mkdir(exist_ok=True)
t='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';binary=b/'NGC_native/NGC_ProofDriver'
cmd=[t+'/bin/lake','env','leanc','-O3','-rdynamic','-o',str(binary),'NGC_native/NGC_ProofDriver.c','NGC_native/NGC_WALKER.c','NGC_native/NGC_MemoryLimit.c']
r=subprocess.run(cmd,capture_output=True,text=True);(out/'link.log').write_text(r.stdout+r.stderr);assert r.returncode==0
results=[]
modes=['fixtures','proof0','proof1','proof2','proof3','proof4'] if os.environ.get('NGC_AUDIT_PART','1')=='1' else ['proof5','proof6','proof7','proof8','scan']
for mode in modes:
 started=time.monotonic();r=subprocess.run([str(binary),mode],capture_output=True,text=True,timeout=120)
 (out/(mode+'.log')).write_text(r.stdout+r.stderr);results.append(dict(mode=mode,exit_status=r.returncode,wall_seconds=time.monotonic()-started))
 print(mode,r.returncode,r.stdout[-900:],flush=True)
 if mode=='fixtures':assert r.returncode==0 and r.stdout.count('NEP_RESULT ')==8,r.stdout
 else:assert r.returncode==0,r.stdout+r.stderr
 for p in b.glob('NEP_'+mode+'_*_REACHABLE.txt'):
  raw=p.read_bytes();(out/(p.name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(out/(p.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'  '+p.name+'\n');p.unlink()
(out/('results'+os.environ.get('NGC_AUDIT_PART','1')+'.json')).write_text(json.dumps(results,indent=1)+'\n')
