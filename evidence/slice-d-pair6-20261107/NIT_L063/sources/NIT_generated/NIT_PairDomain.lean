import NIT_PowersInstantiation
import NIT_ErrorTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PairDomain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts AspisR1Stage2

/-- Only primitive caller facts, never a callee result or pair-output equation. -/
structure Domain (w : W) (alpha : Array E 2#usize) (f : Slice U8) (kappa : E) : Prop where
 s2 : w.variant=FIo_Native.transport.Variant.S2
 factors : NHI_TensorOuterStep.Factors w
 extra : NHI_CellCanon.array w.extra
 alphas : canonical alpha
 words : NIG_FinishInput.Windows f 64
 kappa : canonE kappa

def alpha (p : verifier.Prepared) : Array E 2#usize :=
 NFW_PowersCohort.mapArray FIo_Install.toE p.alpha

theorem alpha_slice (p : verifier.Prepared) : (alpha p).to_slice=FIo_Install.toSlice p.alpha.to_slice := rfl

/-- SAME actual NEW return and SAME actual finish-call primitive Domain. -/
theorem caller (r : NP6_StdModel.Reservation) (proof : Slice U8) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) (input : NIG_FinishInput.Domain proof v p a)
 (w : FIo_Install.W) (new : (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w)) :
 Domain (FIo_Install.toWeights w) (alpha p) v.final_message (FIo_Install.toE p.kappa) := by
 obtain ⟨s2,factors,extra⟩ := NIG_PairInputs.new_owner r proof v p a input w new
 have alphas := NIG_PairInputs.alphas proof v p a input
 change canonical (alpha p) at alphas
 exact ⟨s2,factors,extra,alphas,input.final_words,NIG_FinishAlpha.canonical _ input.kappa⟩

theorem message_size (w : W) (alpha : Array E 2#usize) (f : Slice U8) (kappa : E)
 (h : Domain w alpha f kappa) : f.val.length=2048 := h.words.1

theorem field_domain (w : W) (alpha : Array E 2#usize) (f : Slice U8) (kappa : E)
 (h : Domain w alpha f kappa) (i : Nat) (small : i<64) : NIQ_FieldDomains.Domain f i :=
 NIQ_FieldDomains.windows f 64 i h.words (by omega) small

/-- Exact emitted two-fold body equation on the SAME arbitrary two-element
array. No source result, branch success, or endpoint value is a premise. -/
theorem source [FIo_Native.Allocation] (w : W) (alpha : Array E 2#usize)
 (f : Slice U8) (size : f.val.length=2048) (kappa : E) :
 FIo_Native.weights.Weights.pair w alpha.to_slice f kappa=
 NIG_PairS2Body.reference w alpha.to_slice f kappa := by
 rw [NIG_PairModel.source]
 unfold NIG_PairModel.reference NIG_PairS2Body.reference
 dsimp only
 have alpha_length : Slice.len alpha.to_slice=2#usize :=
  NIG_PairGeometry.length _ _ alpha.property
 rw [NIG_PairGeometry.message_cells f size]
 simp only [alpha_length,bind_tc_ok,NIG_Geometry.expected,
  show (64#usize != 64#usize)=false by decide,Bool.false_eq_true,ite_false,ite_true,
  show ¬(2#usize=1#usize) by decide]
 rfl

#print axioms alpha_slice
#print axioms caller
#print axioms message_size
#print axioms field_domain
#print axioms source
end AspisR1.NIT_PairDomain
