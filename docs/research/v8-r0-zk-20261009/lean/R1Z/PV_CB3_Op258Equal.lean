import R1Z.PV_CB3_Op258Ref
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258Equal
open Aeneas Aeneas.Std Result ProverRwFull
local instance : DecidableEq aspis_core.field.QM31 := Classical.decEq _

theorem source (a b : aspis_core.field.QM31) :
    PV_CB3_Op258Ref.reference.equal a b = ok (decide (a = b)) := by
  rcases a with ⟨⟨a0,a1⟩,⟨a2,a3⟩⟩
  rcases b with ⟨⟨b0,b1⟩,⟨b2,b3⟩⟩
  simp only [PV_CB3_Op258Ref.reference.equal]
  split_ifs <;> simp_all

theorem refl (a : aspis_core.field.QM31) :
    PV_CB3_Op258Ref.reference.equal a a = ok true := by
  simp only [source,decide_true]

theorem symmetric (a b : aspis_core.field.QM31) :
    PV_CB3_Op258Ref.reference.equal a b = PV_CB3_Op258Ref.reference.equal b a := by
  simp only [source,eq_comm]

theorem total (a b : aspis_core.field.QM31) :
    ∃ out, PV_CB3_Op258Ref.reference.equal a b = ok out := ⟨_,source a b⟩
#print axioms source
#print axioms refl
#print axioms symmetric
#print axioms total
end R1Z.PV_CB3_Op258Equal
