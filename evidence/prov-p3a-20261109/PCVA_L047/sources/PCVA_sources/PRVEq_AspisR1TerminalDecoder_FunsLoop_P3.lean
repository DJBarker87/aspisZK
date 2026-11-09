-- PCVA_ P3a (class SOURCE_SHAPE, loop return encoding; FP3-2 of PCUC_FOR_P3.json).
-- Fresh (p2 pass, PCQC_E003) digest_is_canonical_loop returns Option Bool (pending_return); the gate returns Bool.
-- Fresh `aspis_core.field.P` is an opaque `Result U32` in the received fresh emission (FP3-1, owned by P1e).  HYPOTHESIS H_P below:
-- the P1e-transparent form `P = ok <gate P>`.  Every theorem here is conditional on exactly H_P; it is NOT discharged by this file.
import Aeneas
import AspisR1TerminalDecoder.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace PRVFresh_TD
open AspisR1TerminalDecoder

/-- H_P: P1e-transparent fresh form of aspis_core::field::P (conditional hypothesis, see header). -/
def aspis_core.field.P : Result Std.U32 := ok AspisR1TerminalDecoder.aspis_core.field.P

def pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  (digest : Array aspis_core.field.M31 8#usize) (i : Std.Usize) :
  Result (ControlFlow Std.Usize (Option Bool))
  := do
  let s ← lift (Array.to_slice digest)
  let i1 := Slice.len s
  if i < i1
  then
    let m ← Array.index_usize digest i
    let i2 ← PRVFresh_TD.aspis_core.field.P
    if m >= i2
    then ok (done (some false))
    else let i3 ← i + 1#usize
         ok (cont i3)
  else ok (done none)

def pool_v1.pair_forest_accounts.digest_is_canonical_loop
  (digest : Array aspis_core.field.M31 8#usize) (i : Std.Usize) :
  Result (Option Bool)
  := do
  loop
    (fun i1 => PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
      digest i1)
    i

def pool_v1.pair_forest_accounts.digest_is_canonical
  (digest : Array aspis_core.field.M31 8#usize) : Result Bool := do
  let pending_return ←
    PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest 0#usize
  match pending_return with
  | none => ok true
  | some b => ok b

end PRVFresh_TD

namespace PRVP3

def conv : Option Bool → Bool
  | none => true
  | some b => b

/-- body-level refinement: the gate body is the fresh body with the pending-return encoding forgotten. -/
theorem body_refines (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) (i : Std.Usize) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i =
    (PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i) >>= fun cf =>
      ok (match cf with | cont j => cont j | done o => done (conv o)) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body PRVFresh_TD.aspis_core.field.P
  simp only [lift, bind_tc_ok]
  by_cases h : i < Slice.len (Array.to_slice digest)
  · simp only [h, if_true, bind_tc_ok]
    rcases hm : Array.index_usize digest i with m | e | _ <;> simp [hm]
    · by_cases hp : (AspisR1TerminalDecoder.aspis_core.field.P).val ≤ m.val <;> simp [hp, conv]
      rcases hi : (i + 1#usize) with j | e | _ <;> simp [hi]
  · simp only [h, if_false, bind_tc_ok, conv]
#print axioms body_refines
end PRVP3
