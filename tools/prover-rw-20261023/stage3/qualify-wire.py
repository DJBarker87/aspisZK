"""Qualify the generated discriminant instance; preserve every enum code."""
from pathlib import Path
import hashlib,json
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwWireTypes.lean')
s=p.read_text(); before=hashlib.sha256(s.encode()).hexdigest()
assert s.count('@[discriminant isize]')==1
s=s.replace('@[discriminant isize]\n','')
names=['Allocation','RowOrder _ _','InvalidRow','Tag _','Length _','NonCanonical _ _','Boundary _','Terminal','EqualCirclePoints','TrailingBytes','Public','ActivePole']
d='def r1_wire.Error.read_discriminant : r1_wire.Error → Isize\n'
d+=''.join(f'  | .{n} => {i}#isize\n' for i,n in enumerate(names))
d+='\ninstance _root_.ProverRwWire.r1_wire.Error.instDiscriminant :\n    Aeneas.Std.Discriminant r1_wire.Error Isize where\n  read_discriminant := r1_wire.Error.read_discriminant\n\n'
s=s.replace('end ProverRwWire',d+'end ProverRwWire');p.write_text(s)
Path('docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/stage3/wire-discriminant.json').write_text(json.dumps(dict(before_sha256=before,after_sha256=hashlib.sha256(s.encode()).hexdigest(),change='Replace colliding generated discriminant attribute with namespace-qualified instance and identical sequential codes',codes=names),indent=2)+'\n')
