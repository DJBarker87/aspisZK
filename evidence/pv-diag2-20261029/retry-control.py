from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');S=D.parent/'codex-pv-fscan-20261028/src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((D/'native-binding.json').read_text());row=old['source_rows'][0];path=Path(row['path']);assert sha(path)==row['sha256'];assert row['body'] in path.read_text()
template=D/'PV_DIAG2_RetryControl.rs';source=D/'PV_DIAG2_RetryControlGenerated.rs';source.write_text(template.read_text().replace('// PV_DIAG2_CONTROLLER',row['body']))
T=D.parent/'codex-pv-rdea-20261028/client-target/release/deps';rustc=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc');lib=next(T.glob('libaspis_r1_cost_probe-*.rlib'));exe=D/'retry-control'
cmd=[str(rustc),'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','aspis_r1_cost_probe='+str(lib),'-L','dependency='+str(T),str(source),'-o',str(exe)]
print('Expected time: optimized controller-fixture compilation then finite control enumeration; no field arithmetic',flush=True)
subprocess.run(cmd,check=True);run=subprocess.run([str(exe)],capture_output=True,text=True);print(run.stdout,run.stderr);assert run.returncode==0
result=dict(classification='finite validation of byte-identical frozen retry controller with explicit fixture leaf bodies; not a native proof or an honest proving run',source_controller=row,template_sha256=sha(template),generated_source_sha256=sha(source),command=cmd,toolchain=subprocess.check_output([str(rustc),'-vV'],text=True),rlib_sha256=sha(lib),features='exact deployed rlib reused; caller release profile opt3 overflow/debug assertions off panic unwind',results=json.loads(run.stdout),exit=run.returncode,stderr=run.stderr,scope=['full Result including successful attempts count, error variant and state','callback invocation history and body history','closure destructor once on all normal exit routes','no final Rejected despite arbitrary body rejection sequences'],limitations=['generate/prove leaves are explicit fixture operations, not replacements credited as production callees','does not establish honest per-attempt diagnostic silence, native unwind/oom effects or joint retry probabilities'])
(D/'retry-control-validation.json').write_text(json.dumps(result,indent=2)+'\n')
