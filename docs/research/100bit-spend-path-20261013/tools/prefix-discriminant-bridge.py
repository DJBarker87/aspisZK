#!/usr/bin/env python3
"""One-sided, naming-only Lean adapter; never edits the extracted mirror."""
from pathlib import Path
import argparse,hashlib,json
base=Path(__file__).resolve().parents[1]
source=base/'lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Types.lean'
dest=base/'lean/bridge-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Types.lean'
pins=dest.parent.parent/'adapter-pins.json'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
raw=source.read_bytes();assert sha(raw)=='0989c292e546c2da00dc695ee9f34c0bcbfee6cd7ee244ba6008045e155b1e57'
s=raw.decode();attribute='@[discriminant isize]\n';assert s.count(attribute)==1
constructors=[('Allocation',0),('RowOrder _ _',1),('InvalidRow',2),('Tag _',3),('Length _',4),('NonCanonical _ _',5),('Boundary _',6),('Terminal',7),('EqualCirclePoints',8),('TrailingBytes',9),('Public',10)]
end='| Public : r1_wire.Error\n';assert s.count(end)==1
aux='''
-- Naming-only adapter for the extracted discriminant attribute. The pinned
-- generator uses constructor order for values 0..10; its anonymous instance
-- otherwise collides with RecordParser.Types at the global name.
def r1_wire.Error.read_discriminant (x : r1_wire.Error) : Isize :=
  match x with
'''+''.join(f'  | .{name} => {n}#isize\n' for name,n in constructors)+'''
instance _root_.AspisR1PrefixAggregateParser.r1_wire.Error.instDiscriminant :
    Aeneas.Std.Discriminant r1_wire.Error Isize where
  read_discriminant := r1_wire.Error.read_discriminant
'''
adapted=s.replace(attribute,'').replace(end,end+aux)
# Inverse verification protects every pre-existing type/function source byte.
assert adapted.replace(aux,'').replace('inductive r1_wire.Error where',attribute+'inductive r1_wire.Error where')==s
record={'original_source':str(source.relative_to(base)),'original_sha256':sha(raw),'adapter_source':str(dest.relative_to(base)),'adapter_sha256':sha(adapted.encode()),'backend_generator_source':'Aeneas/Data/Discriminant.lean','backend_generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03','generator_rule':'generateReadDiscriminantCmds: ctor order mapIdx; same read_discriminant; only instance name qualified','old_instance':'instDiscriminantErrorIsize','new_instance':'AspisR1PrefixAggregateParser.r1_wire.Error.instDiscriminant','constructor_codes':[list(x) for x in constructors],'original_source_unchanged':True}
args=argparse.ArgumentParser();args.add_argument('--check',action='store_true');a=args.parse_args()
if a.check:
 assert dest.read_text()==adapted
 assert json.loads(pins.read_text())==record
 print('PASS: exact original, one discriminant naming adapter, all original bodies unchanged')
else:
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(adapted);pins.write_text(json.dumps(record,indent=2)+'\n')
 print(dest)
