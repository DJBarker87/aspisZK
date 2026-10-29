from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');T=D.parent/'codex-pv-rdea-20261028/client-target/release/deps';lib=next(T.glob('liblog-*.rlib'));src=D/'PV_DIAG2_LogGuard.rs';exe=D/'log-guard';rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[rustc,'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','log='+str(lib),'-L','dependency='+str(T),str(src),'-o',str(exe)]
print('Expected time: optimized facade-guard probe compilation and ten finite controls',flush=True);subprocess.run(cmd,check=True);r=subprocess.run([str(exe)],capture_output=True,text=True);assert r.returncode==0
out=dict(classification='finite deployed log facade validation; not proof of native dependency logger/filter configuration stability',command=cmd,rlib_sha256=sha(lib),source_sha256=sha(src),toolchain=subprocess.check_output([rustc,'-vV'],text=True),features='log0.4.33 features[]; exact release rlib reused',results=json.loads(r.stdout),open='arbitrary native dependencies may set_max_level/install logger or log directly; current filter/public-state closure remains P')
(D/'log-guard-validation.json').write_text(json.dumps(out,indent=2)+'\n');print(r.stdout)
