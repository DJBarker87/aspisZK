#!/usr/bin/env python3
"""Retain the reached root calls in the existing complete finish proof spine."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
p=B/'lean/bridge-finish-a555-20261017/ExtractedVerifyFinishReachability.lean'
s=p.read_text()
helpers=s[s.index('private theorem bind_success'):s.index('/-- Actual complete finish')]
start=s.index('theorem finish_success');conclusion=s.index(' :\n    ∃ running',start)
header=s[start:conclusion].replace('theorem finish_success','theorem finish_root_calls',1)
body=s[s.index(' := by\n',conclusion)+len(' := by\n'):s.index('\n#print axioms finish_success')]
old='''                          exact ⟨running,t25,record25,record26,z0,t26,z1,t27,
                            hrounds,rfl,rfl,rfl,hclaims,hr25,hextra,hz0,hr26,hbeforeZ1,hz1,rfl⟩'''
new='''                          exact ⟨rootPayload,copied,root2,hroot,hcopy,hroot2,rfl⟩'''
assert body.count(old)==1
body=body.replace(old,new)
spec=''' :
    ∃ (rootPayload : Slice U8)
      (copied : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
      (root2 : Array U8 32#usize),
      FinishModel.payload pre 2#u8 = ok (.Ok rootPayload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootPayload = ok copied ∧
      B.unwrapRoot copied = ok root2 ∧
      out.roots = Array.make 2#usize [pre.c1_root,root2] := by
'''
out='''import S1SemanticFinishModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.S1SemanticFinishRoots

'''+helpers+'''/-- SAME successful complete source-shaped finish, including the actual
row-2 payload, full conversion/unwrap results and both returned roots. No root
identity, separate child success or independently chosen root is a premise.
The proof spine is reused verbatim from FinishCalls.finish_success; only the
terminal projection changes. Concrete native child installation remains open. -/
'''+header+spec+body+'''

#print axioms finish_root_calls
end AspisR1PublicPreparation.S1SemanticFinishRoots
'''
target=B/'lean-candidates/s126-caller-boundary-20261021/S1SemanticFinishRootsV1.lean'
if '--check' in sys.argv:
 assert target.read_text()==out,'generated root projection differs'
 print('finish root projection matches the existing proof spine')
else:target.write_text(out)
