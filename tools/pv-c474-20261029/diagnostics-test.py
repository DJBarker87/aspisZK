"""Finite process/error and matched interposition controls; no private outputs."""
from pathlib import Path
import os,json,hashlib,subprocess,resource
resource.setrlimit(resource.RLIMIT_CORE, (0,0))
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');os.chdir(H)
base=H/'native-target';exe=base/'client/devnet_spend';env=dict(os.environ,RUST_BACKTRACE='full',RUST_LIB_BACKTRACE='1')
rows=[]
for name,request,code,stderr in [('parse',b'not JSON',1,b'client error\n'),('panic',b'{}',-6,b'client panic\n')]:
 r=subprocess.run([exe],input=request,env=env,capture_output=True)
 rows.append(dict(name=name,exit=r.returncode,stderr=r.stderr.decode(),stdout_bytes=len(r.stdout),passed=r.returncode==code and r.stderr==stderr and not r.stdout))
assert all(r['passed'] for r in rows),rows
subprocess.run(['cc','-shared','-fPIC','-O2','interposer.c','-o','libinterposer.so'],check=True)
def rlib(profile,crate,version):
 folder=base/profile/'deps'
 ds=[p for p in folder.glob(crate+'-*.d') if (crate+'-'+version) in p.read_text()]
 if profile=='release':
  ds=[p for p in ds if json.loads((base/profile/'.fingerprint'/p.stem/('lib-'+crate+'.json')).read_text())['rustflags']==['-C','link-arg=-Wl,--threads=4']]
 # Cached release fingerprints can differ in transitive libc versions.
 # Control only: select std-enabled getrandom 0.3.4, same fallback source.
 if profile=='release' and crate=='getrandom':
  ds=[p for p in ds if json.loads((base/profile/'.fingerprint'/p.stem/('lib-'+crate+'.json')).read_text())['features']=='[\"std\"]']
 assert len(ds)==1,(profile,crate,ds)
 return folder/('lib'+ds[0].stem+'.rlib')
controls=[]
for label,profile in [('direct','client'),('fallback-control','release')]:
 cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','panic=abort','probe.rs','-L','dependency='+str(base/profile/'deps'),'--extern','getrandom='+str(rlib(profile,'getrandom','0.3.4')),'--extern','anyhow='+str(rlib(profile,'anyhow','1.0.104')),'-L','native='+str(H),'-l','dylib=interposer','-C','link-arg=-Wl,-rpath,'+str(H),'-o',str(H/('probe-'+label))]
 subprocess.run(cmd,check=True)
 r=subprocess.run([H/('probe-'+label)],env=dict(env,LD_PRELOAD=str(H/'libinterposer.so')),capture_output=True,text=True,check=True)
 expected='ok=true counts=0\n' if label=='direct' else 'ok=false counts=4294967297\n'
 assert r.stdout==expected,(label,r.stdout,r.stderr)
 oom=subprocess.run([H/('probe-'+label),'oom'],env=env,capture_output=True)
 assert oom.returncode==-6 and not oom.stdout and not oom.stderr,(label,'allocation diagnostic',oom.returncode,oom.stderr)
 controls.append(dict(oom_exit=oom.returncode,oom_stderr_bytes=len(oom.stderr),label=label,command=cmd,stdout=r.stdout,binary_sha256=hashlib.sha256((H/('probe-'+label)).read_bytes()).hexdigest()))
result=dict(client_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),process_tests=rows,controls=controls,scope='Finite validation. The direct harness links the identical getrandom/anyhow rlibs used by the client; baseline is the matched interposition control. Environment starts enabled, then is re-enabled after initialize; both std and anyhow remain disabled.')
(H/'diagnostics-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
