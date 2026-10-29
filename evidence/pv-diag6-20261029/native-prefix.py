from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag6-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=D/'native-prefix.rs';exe=D/'native-prefix';cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no',str(src),'-o',str(exe)]
subprocess.run(cmd,check=True);p=subprocess.run([str(exe)],text=True,capture_output=True);print(p.stdout,p.stderr);assert p.returncode==0
v=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-Vv'],text=True)
(D/'native-controls.json').write_text(json.dumps(dict(classification='finite native validation; std-only harness, not application codegen equality or a universal joint law',command=cmd,source_sha256=sha(src),binary_sha256=sha(exe),toolchain=v,output=p.stdout,exit=p.returncode,scope='partial-write effect prefixes for fixed inputs; no divergence runtime claim',features='std-only; application deployed feature inventory inherited in source-bindings.json',compiler_boundary='V370 retained'),indent=2)+'\n')
