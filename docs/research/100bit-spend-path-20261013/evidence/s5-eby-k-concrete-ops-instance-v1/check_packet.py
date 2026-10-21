#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parents[4]
p=Path(__file__).resolve().parent
orig=(p/'sources/AspisR1WeightsPairCut/Types.original.lean').read_text()
adapt=(p/'sources/AspisR1WeightsPairCut/Types.lean').read_text()
variant_old="""@[discriminant isize]
inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant
"""
variant_new="""inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant

-- Explicitly namespaced expansion of the pinned Aeneas discriminant reader.
def transport.Variant.read_discriminant (x : transport.Variant) : Isize :=
  match x with
  | .S1 => 0#isize
  | .S2 => 1#isize
  | .D => 2#isize

instance _root_.AspisR1WeightsPairCut.transport.Variant.instDiscriminant :
    Aeneas.Std.Discriminant transport.Variant Isize where
  read_discriminant := transport.Variant.read_discriminant
"""
error_old="""@[discriminant isize]
inductive verifier.Error where
| Parse : verifier.Error
| Allocation : verifier.Error
"""
error_new="""inductive verifier.Error where
| Parse : verifier.Error
| Allocation : verifier.Error

-- Explicitly namespaced expansion of the pinned Aeneas discriminant reader.
def verifier.Error.read_discriminant (x : verifier.Error) : Isize :=
  match x with
  | .Parse => 0#isize
  | .Allocation => 1#isize

instance _root_.AspisR1WeightsPairCut.verifier.Error.instDiscriminant :
    Aeneas.Std.Discriminant verifier.Error Isize where
  read_discriminant := verifier.Error.read_discriminant
"""
assert orig.count(variant_old)==1 and orig.count(error_old)==1
expected=orig.replace(variant_old,variant_new).replace(error_old,error_new)
assert expected==adapt, 'WPC Types changed outside the two enumerated discriminant adapters'
assert (p/'sources/AspisR1WeightsPairCutEbyKDotOpsV1.lean').read_bytes()==Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean-candidates/s3-whole-pair-typed-ops-v26-20261021/sources/AspisR1WeightsPairCutEbyKDotOpsV1.lean').read_bytes()
checks={}
for f in sorted((p/'sources').rglob('*.lean')):
 checks[str(f.relative_to(p))]=hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((p/'manifest.json').read_text()) if (p/'manifest.json').exists() else {}
if manifest:
 for rel,h in manifest.get('source_sha256',{}).items():
  assert checks.get(rel)==h, f'source pin mismatch: {rel}'
print(json.dumps({'ok':True,'type_adapter_only_enumerated_changes':True,'source_hashes':checks},indent=2))
