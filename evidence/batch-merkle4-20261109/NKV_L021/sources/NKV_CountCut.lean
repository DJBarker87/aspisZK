import NKV_FRef
import Port3_BatchStd
set_option autoImplicit false
namespace NKV_CountCut
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Reviewed node_count-return segment: .ok_or(Error::Merkle)? at frozen
candidate.rs:196. Complete Option reply, no successful-count premise. Native
pair NKV_K011/K012; later slot/padding/verify operations are outside this cut. -/
def reply : Option Usize → core.result.Result Usize verifier.Error
 | none => .Err .Merkle | some value => .Ok value

structure Cut (counted : Option Usize)
 (out : core.result.Result Usize verifier.Error) : Prop where
 result : out=reply counted

theorem source (counted : Option Usize)
 (out : core.result.Result Usize verifier.Error) (cut : Cut counted out) :
 AspisR1.Port3_BatchStd.okOr counted verifier.Error.Merkle=ok out := by
 rw [cut.result]
 cases counted <;> rfl

theorem missing (out : core.result.Result Usize verifier.Error) (cut : Cut none out) :
 out=.Err .Merkle := cut.result

theorem present (count : Usize) (out : core.result.Result Usize verifier.Error)
 (cut : Cut (some count) out) : out=.Ok count := cut.result

set_option pp.proofs false
#print source
#print axioms source
#print axioms missing
#print axioms present
end NKV_CountCut
