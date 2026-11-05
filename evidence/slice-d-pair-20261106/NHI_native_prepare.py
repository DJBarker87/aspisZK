"""Reconstruct scratch-only harness inputs from the committed patch and pinned predecessor.
Harness source is retained only in the patch and per-attempt receipt snapshots.
"""
from pathlib import Path
import json,hashlib,difflib,subprocess,sys
E=Path(__file__).resolve().parent;M=E.parent/'slice-d-finish-20261105';C='crates/aspis-r1-cost-probe/src/'
inputs=json.loads((M/'NGM_NATIVE_INPUTS.json').read_text())
target=sys.argv[3] if len(sys.argv)>3 else '';group=int(target.rsplit('g',1)[-1]) if target.startswith('weights::NHI_tensor::g') else -1
patch=(E/('NHI_harness_control.patch' if group>=52 else 'NHI_harness_direct_prestate.patch' if group>=4 else 'NHI_harness.patch')).read_text();marker='+++ b/'+C+'NHI_tensor.rs\n';assert patch.count(marker)==1
section=patch.split(marker,1)[1].split('\n--- ',1)[0]
code=''.join(l[1:]for l in section.splitlines(True)if l.startswith('+')and not l.startswith('+++'))
assert code.startswith('use super::*;\n')
inputs[C+'NHI_tensor.rs']=code;inputs[C+'weights.rs']+='\n#[cfg(kani)] #[path="NHI_tensor.rs"] mod NHI_tensor;\n'
pins={n:hashlib.sha256(t.encode()).hexdigest()for n,t in inputs.items()}
reconstructed=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 reconstructed+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
assert ''.join(reconstructed)==patch,'STOP patch reconstruction mismatch'
