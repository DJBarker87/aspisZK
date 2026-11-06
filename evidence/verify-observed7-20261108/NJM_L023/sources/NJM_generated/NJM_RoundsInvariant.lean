import NJM_RoundNative
import NJG_RoundsUnrolled
set_option autoImplicit false
namespace AspisR1.NJM_RoundsInvariant
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (Code run)
attribute [local irreducible] S1SemanticCode.roundStep

/-- Actual carry passed by the driver, with the canonical earlier prefix. -/
def Inv {H : Type} (n : Nat) (carry : Carry H) : Prop :=
 NJG_CanonicalPrefix.CanonicalBefore carry.2.1 n

/-- Rule-B one-step invariant uses the SAME source Result; no independent
chosen alpha/post is introduced. This is an internal success-arm lemma. -/
theorem step {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (carry next : Carry H) (r : Usize) (bound : r.val<10)
 (before : Inv r.val carry)
 (success : (run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)).2=ok (.Ok next)) :
 Inv (r.val+1) next := by
 have erased : RoundModel.step NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r=ok (.Ok next) := by
  rw [PreparedHashCode.run_value,S1SemanticCode.roundStep_erasure] at success
  exact success
 exact NJG_CanonicalPrefix.step NJM_RoundJoin.R D pre carry.2.2 next.2.2 carry.2.1 next.2.1 carry.1 next.1 r bound before erased

/-- Complete result of the original chain, including prefix effects. -/
theorem cons_run {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (carry : Carry H) (r : Usize) (rest : List Usize) :
 run (chain NJM_RoundJoin.R D pre (r::rest) carry)=
 NGX_RunBind.appendResult
  (run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)).1
  (run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)).2
  (fun reply=>match reply with
   | .Ok next=>chain NJM_RoundJoin.R D pre rest next
   | .Err e=>pure (.Err e)) := by
 rw [NJG_RoundsUnrolled.one,NGX_RunBind.bind_run]
 apply NJG_RoundCode.append_congr
 intro reply
 cases reply <;> rfl

#print axioms step
#print axioms cons_run
end AspisR1.NJM_RoundsInvariant
