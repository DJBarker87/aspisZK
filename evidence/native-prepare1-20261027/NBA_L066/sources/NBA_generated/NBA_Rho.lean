import NBA_Installed
import LPk_Induction
set_option autoImplicit false
namespace AspisR1.NBA_Rho
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open SamplerMachineBounds SamplerRepeatedPass SourceSamplerByteRank

def coordinates (q : aspis_core.field.QM31) : List Nat :=
  [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]

theorem coordinates_injective (x y : aspis_core.field.QM31)
    (eqn : coordinates x=coordinates y) : x=y := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  simp only [coordinates,List.cons.injEq] at eqn
  have ha := UScalar.eq_of_val_eq eqn.1
  have hb := UScalar.eq_of_val_eq eqn.2.1
  have hc := UScalar.eq_of_val_eq eqn.2.2.1
  have hd := UScalar.eq_of_val_eq eqn.2.2.2.1
  cases ha; cases hb; cases hc; cases hd
  rfl

/-- The exact same generic division trace used for the CLOSED eight-digit leaf
is used here at four callbacks. No whole rho function equation is a premise. -/
theorem four_digits (block : Array U8 32#usize) (digits : List Nat) (last : List UInt32)
    (trace : LPk_Induction.Digits 4 (SamplerBytePass.digits block) digits last) :
    digits=SamplerNatModel.qm31Digits (rank block) := by
  have eqn := congrArg Prod.fst (LPk_Induction.digits_join trace)
  dsimp only [Prod.fst] at eqn
  rw [eqn,run_digits]
  rw [SourceSamplerByteRank.word_value]
  rfl

/-- All four native returned coordinates, tied to the SAME four callback
trace, determine the entire actual cohort Result. -/
theorem source (block : Array U8 32#usize) (digits : List Nat) (last : List UInt32)
    (q : aspis_core.field.QM31)
    (trace : LPk_Induction.Digits 4 (SamplerBytePass.digits block) digits last)
    (packed : coordinates q=digits) : sampler.qm31_sample block=ok q := by
  obtain ⟨out,call,canonical,value⟩ := SamplerTransport.sample_total block
  have value' : coordinates out=SamplerNatModel.qm31Digits (rank block) := value
  have same := coordinates_injective q out (packed.trans ((four_digits block digits last trace).trans value'.symm))
  simpa only [same] using call

#print axioms coordinates_injective
#print axioms four_digits
#print axioms source
end AspisR1.NBA_Rho
