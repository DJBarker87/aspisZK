import NDO_JGv_PairShared1
import NDO_JGq_Low
import NDO_JGs_Inactive
import NDO_JGs_LibraSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_PairShared2
open Aeneas Aeneas.Std Result ControlFlow
open JGq_PairShape
abbrev E := FIo_Install.NE
def write (parts : Array E 7#usize) : Array E 7#usize := parts.set 0#usize JGs_Inactive.pair12
def remaining (parts : Array E 7#usize) : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
  let out ← FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f (write parts) JGs_LibraEnd.value
  let sum ← FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} out JGq_PowersK.a7 FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
  ok (.Ok sum)
theorem source (parts : Array E 7#usize) : JGv_PairShared1.low parts=remaining parts := by
  have variant : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant .S2=ok true := by
    change FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true
    unfold FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.read_discriminant
    simp only [eq_self,decide_true]
  have powers : FIo_Native.weights.powers 7#usize kappa=ok JGq_PowersK.a7 := by
    with_unfolding_all exact JGq_PowersK.source
  have inactive : FIo_Native.weights.grouped_inactive_pair w f JGq_Low.a16=ok JGs_Inactive.pair12 := JGs_Inactive.source
  have libra : FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4 w.extra=ok JGs_LibraEnd.value := by
    with_unfolding_all exact JGs_LibraSource.source
  have update : Array.update parts 0#usize JGs_Inactive.pair12=ok (write parts) := by
    obtain ⟨after,call,value⟩ := WP.spec_imp_exists (Array.update_spec parts 0#usize JGs_Inactive.pair12 (by scalar_tac))
    subst after
    exact call
  unfold JGv_PairShared1.low remaining
  simp only [JGq_Low.source,variant,powers,inactive,libra,update,bind_tc_ok,ite_true]
#print axioms source
/-- Exact forward Pair prefix; only the final Libra contraction and seven-part sum remain. -/
theorem native_remaining : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))
    w alpha f kappa=remaining (JGq_SharedHigh.write JGs_K4.parts) := by
  rw [JGq_PairPrefix.native,JGv_PairShared0.source,JGv_PairShared1.source,source]
#print axioms native_remaining
end AspisR1.JGv_PairShared2
end
