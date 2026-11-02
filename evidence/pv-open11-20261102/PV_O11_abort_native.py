from pathlib import Path
import subprocess,json,hashlib,resource
D=Path(__file__).parent
rust='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
commands=[];bins={}
for panic in ['abort']:
 out=D/('PV_O11_abort_'+panic)
 cmd=[rust,'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic='+panic,'-Clink-arg=-Wl,--threads=4',str(D/'PV_O11_abort_native.rs'),'-o',str(out)]
 subprocess.run(cmd,check=True,capture_output=True);commands.append(cmd);bins[panic]={'sha256':sha(out),'bytes':out.stat().st_size}
def no_core():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 resource.setrlimit(resource.RLIMIT_AS,(268435456,268435456))
results=[]
for profile,mode,code,err in [('abort','oom',-6,'')]:
 r=subprocess.run([str(D/('PV_O11_abort_'+profile)),mode],capture_output=True,text=True,preexec_fn=no_core,timeout=30)
 results.append(dict(profile=profile,mode=mode,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,expected_exit=code,expected_stderr=err,ok=r.returncode==code and r.stderr==err and not r.stdout))
j=dict(toolchain=subprocess.check_output([rust,'-vV'],text=True),commands=commands,binaries=bins,source_sha256=sha(D/'PV_O11_abort_native.rs'),diagnostics_sha256=sha(D/'inputs/client/diagnostics.rs'),results=results,ok=all(x['ok'] for x in results),classification='finite validation of adopted source-identical diagnostic module under deployed release settings; OOM-only changed experiment: black-boxed request/pointer and explicit 256MiB address-space limit, no repeated successful fixture cases; no whole-client or witness-independence claim',features='standalone std fixture; exact client diagnostic module has no Cargo feature guards; native std 1.94.1, profile panic=abort,opt3,overflow_checks=false,debug_assertions=false; no project prover execution',expected_time='optimized tiny fixture compilation and one subprocess with RLIMIT_AS=256MiB and a black-boxed 1GiB request, not proof generation or an arithmetic gate')
(D/'PV_O11_abort-oom-result.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['ok','classification']}));assert j['ok']
