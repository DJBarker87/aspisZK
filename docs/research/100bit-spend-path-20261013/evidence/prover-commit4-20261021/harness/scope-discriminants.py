#!/usr/bin/env python3
"""Replace the unused global-name discriminant macro with its explicit,
namespace-scoped 0..4 definition. Constructors and Rust discriminants are
unchanged; this avoids a generated instance-name collision between cones.
"""
from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProverCommitReference/Types.lean')
s=p.read_text()
assert s.count('@[discriminant isize]')==1
s=s.replace('@[discriminant isize]\n','')
needle='| Layout : state_only_hiding.StateOnlyMaskBuildError\n'
replacement=needle+'''
-- Explicit expansion of the discriminant attribute, with a scoped instance name.
def state_only_hiding.StateOnlyMaskBuildError.read_discriminant :
    state_only_hiding.StateOnlyMaskBuildError → Isize
  | .ZeroPrivateEntropy => 0#isize
  | .ReusedMaskNonce => 1#isize
  | .MaskSampleExhausted => 2#isize
  | .TraceShape => 3#isize
  | .Layout => 4#isize

instance instCommitReferenceMaskErrorDiscriminant :
    Discriminant state_only_hiding.StateOnlyMaskBuildError Isize where
  read_discriminant := state_only_hiding.StateOnlyMaskBuildError.read_discriminant
'''
assert s.count(needle)==1
p.write_text(s.replace(needle,replacement))
