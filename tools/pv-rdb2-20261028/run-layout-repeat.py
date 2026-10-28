from pathlib import Path
import subprocess,os,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028')
env=dict(os.environ,RUSTUP_TOOLCHAIN='1.94.1',RUSTC_BOOTSTRAP='1',PATH='/home/dombarker/.cargo/bin:'+os.environ.get('PATH',''))
cmd=['/home/dombarker/.cargo/bin/rustc','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind',str(D/'layout-repeat.rs'),'-o',str(D/'layout-repeat')]
(D/'layout-repeat-inputs.json').write_text(json.dumps(dict(command=cmd,toolchain='rustc1.94.1',source_sha256=hashlib.sha256((D/'layout-repeat.rs').read_bytes()).hexdigest(),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',features='no project Cargo crates; prebuilt std/alloc/core; alloc_layout_extra enables access to the unchanged deployed std body',instrumentation='RUSTC_BOOTSTRAP=1 for unstable API visibility only',expected_time='small optimized std-only compilation then seven finite layout cases',evidence_class='finite native confirmation of restated unpadded/padded laws; not a finding against a padded-layout row'),indent=2)+'\n')
subprocess.run(cmd,env=env,check=True)
subprocess.run([str(D/'layout-repeat')],check=True)
