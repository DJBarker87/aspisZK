import R1Z.PV_CB3_GammaCanonical
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_GammaConstructor
open Aeneas Aeneas.Std Result ProverRwFull

theorem identity (x : aspis_core.field.wide_exact.WideExact)
    (h : PV_CB3_NormalizeIdentity.Canonical x.c0 ∧ PV_CB3_NormalizeIdentity.Canonical x.c1) :
    PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new x.c0 x.c1 = ok x := by
  rcases x with ⟨a,b⟩
  simp only [PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new,
    PV_CB3_NormalizeIdentity.source a h.1,PV_CB3_NormalizeIdentity.source b h.2,bind_tc_ok]

/-- The reference output is already in the constructor's canonical domain. -/
theorem result_stable (block : Array U8 32#usize) :
    PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new
      (PV_CB3_StagedGammaRank.result block).c0 (PV_CB3_StagedGammaRank.result block).c1 =
      ok (PV_CB3_StagedGammaRank.result block) :=
  identity _ (PV_CB3_GammaCanonical.result_canonical block)
#print axioms identity
#print axioms result_stable
end R1Z.PV_CB3_GammaConstructor
