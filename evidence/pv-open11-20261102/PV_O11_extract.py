from pathlib import Path
import subprocess,json,hashlib,os
D=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=D.parent/'codex-pv-extract-20261027/charon'
a=D.parent/'codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2'
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(a)=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
cmd=[str(c),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::kind','--include','std::io::error','--include','std::sys::io::error','--include','core::io::error','--dest-file',str(D/'extract/PV_O11_ErrorKind.llbc'),'--','--manifest-path',str(D/'extract/Cargo.toml'),'--release','--locked','--offline','--lib','--jobs','4']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(D/'charon-target'),CARGO_PROFILE_RELEASE_OPT_LEVEL='3',CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS='false',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='false')
j=dict(command=cmd,charon_sha256=sha(c),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',translator_authority='codex/pv-b3p6-20261028:evidence/pv-b3p6-20261028/resume17/translator-identity-authority.json',extractor_toolchain='nightly-2026-06-01',deployed_toolchain='1.94.1',features=[dict(crate='pv-o11-error-kind',features=[],dependencies='std only')],profile=dict(opt_level=3,panic='abort',debug_assertions=False,overflow_checks=False),scope='direct std getter extraction; no project source edits or dependency substitution. x-prime std source comparison still required',expected_time='optimized compilation and Charon translation; no arithmetic gate')
(D/'PV_O11_extract-input.json').write_text(json.dumps(j,indent=2)+'\n')
p=subprocess.run(cmd,env=env);j['exit']=p.returncode
llbc=D/'extract/PV_O11_ErrorKind.llbc'
if llbc.exists():j.update(llbc_sha256=sha(llbc),llbc_bytes=llbc.stat().st_size)
(D/'PV_O11_extract-result.json').write_text(json.dumps(j,indent=2)+'\n');raise SystemExit(p.returncode)
