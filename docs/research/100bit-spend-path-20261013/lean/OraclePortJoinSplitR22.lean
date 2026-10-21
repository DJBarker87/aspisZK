import R22TotalReducerExecution

/-! Every checked total cone can supply R22 with its operational translation.
Equality of a final oracle Program is deliberately not such a translation. -/
set_option autoImplicit false
namespace AspisR1.OraclePortJoinSplitR22
open Aeneas Aeneas.Std Result R22TotalCheckedComposition

def TotalJoin {ι α : Type} (source : ι → Result α) (model : ι → α) : Prop :=
  ∀ x, source x = ok (model x)

theorem total_join_R22 {ι α : Type} (source : ι → Result α) (model : ι → α)
    (total : TotalJoin source model) (p6 : Translation source) :
    ∀ x, NoOverflow (p6.code x) ∧ wrapping (p6.code x) = ok (model x) := by
  apply total_refinement_R22
  intro x
  exact (p6.source x).trans (total x)

/-- Existing concrete S5 machine-code corollary: all stored U32 pairs,
including noncanonical ones. No new Translation hypothesis for this leaf. -/
theorem m31_multiply (x y : U32) :
    ∃ z, NoOverflow (R22TotalReducerExecution.multiplyCode x y) ∧
      wrapping (R22TotalReducerExecution.multiplyCode x y) = ok z ∧
      z.val = x.val*y.val % AspisV8R17.RawReducer.P ∧
      z.val < AspisV8R17.RawReducer.P :=
  R22TotalReducerExecution.wrapping_multiply_exact x y

#print axioms total_join_R22
#print axioms m31_multiply
end AspisR1.OraclePortJoinSplitR22
