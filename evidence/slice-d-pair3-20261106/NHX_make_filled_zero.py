from pathlib import Path
import subprocess,difflib,runpy,sys
E=Path(__file__).resolve().parent
sys.argv=['NHX_make_filled_zero.py','','','NHX_filled::zero64_window']
inputs=runpy.run_path(str(E/'NHX_native_prepare.py'))['inputs']
C='crates/aspis-core/src/'
# Keep prior failed/general shapes immutable in their snapshots. Add a distinct
# actual-caller domain: n64, Native QM31 ZERO, empty returning reserve prefix,
# inductive zero prefix and arbitrary spare storage.
text=inputs[C+'NHX_filled.rs']
marker='use crate::field::{QM31 as NativeQ'
if marker in text:text=text[:text.index(marker)]
inputs[C+'NHX_filled.rs']=text+(E/'NHX_filled_zero.rs.txt').read_text()
patch=''
for n in[C+'lib.rs',C+'NHX_filled.rs']:
 r=subprocess.run(['git','show','4bb3b3f:'+n],text=True,capture_output=True)
 patch+=''.join(difflib.unified_diff(r.stdout.splitlines(True),inputs[n].splitlines(True),fromfile='a/'+n if r.returncode==0 else'/dev/null',tofile='b/'+n))
(E/'NHX_filled.patch').write_text(patch)
