from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();exe=D/'native-controls'
src=D/'PV_DIAG5_NativeControls.rs';tool='/home/dombarker/.cargo/bin/rustc'
cmd=[tool,'+1.94.1','--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind',str(src),'-o',str(exe)]
subprocess.run(cmd,check=True);result=subprocess.check_output([str(exe)],text=True);print(result)
(D/'native-controls.json').write_text(json.dumps(dict(classification='finite native validation; reference first-match enumeration, actual std disabled/forced formatting',command=cmd,source_sha256=sha(src),binary_sha256=sha(exe),binary_bytes=exe.stat().st_size,rustc=subprocess.check_output([tool,'+1.94.1','-Vv'],text=True),profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False,panic='unwind'),features='std-only controls; no application linkage; no whole-deployed-application credit',deployed_units='inherited evidence/pv-diag-20261029/resolved-build-units.json',source_to_machine='V370 / D381/D386 retained',stdout=result),indent=2)+'\n')
