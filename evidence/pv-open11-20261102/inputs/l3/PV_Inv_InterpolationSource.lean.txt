import R1Z.PV_Inv_IInterpolationInitial
import R1Z.PV_Inv_NativeInverseM
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_InterpolationSource
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitM31Ops48

theorem source_inverse_operand (i : U8) (bound : i.val<28) :
    ∃ (basis : Array U32 28#usize) (den inv : U32),
      PV_Inv_IInterpolationInitial.prepare i=ok (basis,den) ∧ canonical den ∧
      den ≠ 0#u32 ∧ inverse_ref den=ok inv ∧ canonical inv := by
  obtain ⟨basis,den,hprep,hbasis,hden,hpoly,hvalue,hn⟩ :=
    PV_Inv_IInterpolationInitial.prepare_exact i bound
  obtain ⟨inv,hinv,hcan,hval⟩ := ProverCommitInterpolationInverse48.inverse_exact den hn
  exact ⟨PV_Inv_IM31Array.array 28#usize basis,den,inv,hprep,hden,hn,hinv,hcan⟩

#print axioms source_inverse_operand
end R1Z.PV_Inv_InterpolationSource
