import R1Z.PV_CompressTransport
import R1Z.PV_CurrentScaleInstall
import R1Z.ProverRwP7CompressPrimitives
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressLastPower
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
abbrev selected := PV_CurrentScaleInstall.selected

theorem mul_total (ops : ExternalFuns) (a b : Q) :
    ∃ c, (selected ops).op69 a b = ok c := by
  change ∃ c, PV_CurrentQuarticBridge.S.mul a b = ok c
  rw [PV_CurrentQuarticBridge.mul]
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.mul (toQ a) (toQ b)
  refine ⟨fromQ c,?_⟩
  change mapResult fromQ (AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)) = ok (fromQ c)
  rw [hc]
  rfl

-- Erasure is proved under the installed total multiplication, never arbitrary ops.
theorem erase (ops : ExternalFuns) (out power lambda : Q) :
    (do let _ ← (selected ops).op69 power lambda; ok out) = ok out := by
  obtain ⟨c,hc⟩ := mul_total ops power lambda
  rw [hc]
  rfl

theorem singleton (ops : ExternalFuns) (m : U32) (lambda out power : Q) :
    @PV_CompressList.fold _ (selected ops) [m] lambda out power = (do
      let q ← (selected ops).op70 power m
      let out1 ← (selected ops).op67 out q
      ok out1) := by
  letI : ExternalFuns := selected ops
  rw [@PV_CompressList.cons _ (selected ops) m [] lambda out power]
  simp only [PV_CompressList.nil]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro out1 _
  exact erase ops out1 power lambda
theorem empty (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q)
    (h : values.val=[]) :
    @ProverRwP6CompressSource.compress _ (selected ops) tag values lambda = (do
      let c ← (selected ops).op61 tag
      let out ← (selected ops).op66 c
      ok out) := by
  letI : ExternalFuns := selected ops
  rw [@ProverRwP6CompressControl.compress_finite _ (selected ops) tag values lambda]
  have hl : (Slice.len values).val=0 := by change values.val.length=0; rw [h]; rfl
  simp only [hl,ProverRwP6CompressControl.finite,ProverRwP6CompressControl.dispatch]
  have hn : ¬ (0#usize) < Slice.len values := by change ¬ 0 < (Slice.len values).val; omega
  simp only [hn,if_false]
#print axioms empty
#print axioms mul_total
#print axioms erase
#print axioms singleton
end R1Z.PV_CompressLastPower
