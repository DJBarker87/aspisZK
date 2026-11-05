"""Own scratch inputs, full frozen manifest pins, no shared source changes."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
x={}
for name in ['lib','candidate']:
 t=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/'+name+'.rs'],text=True)
 if name=='lib':t=t.replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')
 t+='\n#[cfg(kani)] '+('include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n' if name=='lib' else '#[path="NID_native.rs"] mod NID_native;\n')
 x['crates/aspis-r1-cost-probe/src/'+name+'.rs']=t
x['crates/aspis-r1-cost-probe/src/NID_native.rs']=(E/'NID_native.rs.txt').read_text()
# Existing cfg(kani) literal path inputs: immutable retained NHV source, not credited.
old=json.loads(Path('evidence/tx2-native-20261106/NHV_NATIVE_INPUTS.json').read_text())
for n,t in old.items():
 if n.startswith('tools/'):x[n]=t
(E/'NID_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
pins={n:r['sha256'] for n,r in json.loads(Path('evidence/extract-stage-20261106/NHR_STAGING_MANIFEST.json').read_text())['files'].items()}
pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()})
(E/'NID_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
