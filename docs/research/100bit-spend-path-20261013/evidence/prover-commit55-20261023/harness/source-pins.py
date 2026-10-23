from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={}
for path in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/r0/scalar.rs','crates/aspis-r1-cost-probe/src/sim.rs','crates/aspis-statement/src/state_only_poseidon.rs','crates/aspis-statement/src/poseidon2.rs']:
 p=Path(path);pins[path]=dict(sha256=sha(p),bytes=p.stat().st_size)
copies=[]
for pkg in ['guard-owner','native','native-components','native-caller','native-constructors','native-poseidon','native-projections']:
 for name,src in [('field.rs','crates/aspis-core/src/field.rs'),('field/wide_exact.rs','crates/aspis-core/src/field/wide_exact.rs')]:
  p=E/pkg/name
  if p.exists():
   assert p.read_bytes()==Path(src).read_bytes(),p
   copies.append(dict(copy=str(p),frozen=src,sha256=sha(p)))
assert subprocess.check_output(['git','diff','341584654f','--name-only','--','crates','programs'])==b''
r=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),pins=pins,byte_identical_copies=copies,shipped_changes=False,note='Harness/interface projection and source-cut boundaries remain explicit; byte-identical field source is not a whole native simulator proof.')
(E/'final-source-pins.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(pins=len(pins),byte_identical_copies=len(copies),shipped_changes=False)))
