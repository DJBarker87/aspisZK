import R1Z.PV_CompressModel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressModelTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

theorem stateFold (values : List M) (lambda : Q) (state : Q × Q)
    (scale : ∀ a b, ∃ c, aspis_core.field.QM31.mul_m31 a b = ok c)
    (add : ∀ a b, ∃ c, aspis_core.field.QM31.add a b = ok c)
    (mul : ∀ a b, ∃ c, aspis_core.field.QM31.mul a b = ok c) :
    ∃ result, PV_CompressList.stateFold values lambda state = ok result := by
  induction values generalizing state with
  | nil => exact ⟨state,rfl⟩
  | cons m ms ih =>
    rcases state with ⟨out,power⟩
    obtain ⟨q,hq⟩ := scale power m
    obtain ⟨o,ho⟩ := add out q
    obtain ⟨p,hp⟩ := mul power lambda
    obtain ⟨r,hr⟩ := ih (o,p)
    exact ⟨r,by simp only [PV_CompressList.stateFold,hq,ho,hp,bind_tc_ok]; exact hr⟩
#print axioms stateFold
end R1Z.PV_CompressModelTotal
