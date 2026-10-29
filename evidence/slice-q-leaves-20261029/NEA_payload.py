"""Own scratch payload updates; archive exact baseline-relative patch."""
from pathlib import Path
import json,subprocess,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',REV+':'+p],stderr=subprocess.DEVNULL,text=True)
def save(payload):
 (E/'NEA_PAYLOAD.json').write_text(json.dumps(payload))
 patch=''
 for p,s in payload.items():
  try:old=frozen(p)
  except subprocess.CalledProcessError:old=''
  patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p if old else '/dev/null',tofile='b/'+p))
 (E/'NEA_native.patch').write_text(patch)
if __name__=='__main__':
 payload=json.loads((E/'NEA_PAYLOAD.json').read_text())
 for crate in ['aspis-core','aspis-r1-cost-probe']:
  p=f'crates/{crate}/src/lib.rs';s=frozen(p)
  s='#![cfg_attr(kani, feature(allocator_api))]\n'+s
  s+='\n#[cfg(kani)] pub(crate) mod NEA_copy { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n'
  payload[p]=s
 save(payload)
