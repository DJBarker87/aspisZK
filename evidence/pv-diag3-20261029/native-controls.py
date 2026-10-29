from pathlib import Path
import subprocess,json,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-diag3-20261029');T=D.parent/'codex-pv-rdea-20261028/client-target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rustc=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc');src=D/'PV_DIAG3_NativeControls.rs';anyhow=next(T.glob('libanyhow-*.rlib'));exe=D/'native-controls'
cmd=[str(rustc),'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','anyhow='+str(anyhow),'-L','dependency='+str(T),str(src),'-o',str(exe)]
print('Expected time: optimized control compilation and small std/anyhow executions; no proof generation or arithmetic',flush=True)
subprocess.run(cmd,check=True)
env=dict(os.environ,RUST_BACKTRACE='0',RUST_LIB_BACKTRACE='0');r=subprocess.run([str(exe)],env=env,capture_output=True)
record=dict(classification='finite native validation; actual deployed std and anyhow rlib, scripted writer and cleanup fixtures, not whole honest-run proof',command=cmd,toolchain=subprocess.check_output([str(rustc),'-vV'],text=True),source_sha256=sha(src),rlib_sha256=sha(anyhow),binary_sha256=sha(exe),exit=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode(),features='deployed anyhow rlib from rdea, original resolved-build-units.json; std 1.94.1; harness opt3 overflow/debug assertions off panic unwind',singleton_evidence=False)
(D/'native-controls.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['stdout'],record['stderr']);assert r.returncode==0
