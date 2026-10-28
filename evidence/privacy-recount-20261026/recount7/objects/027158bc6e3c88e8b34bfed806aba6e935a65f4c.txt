import R1Z.PV_RunJoin_SourceModel20
import R1Z.PV_Src_RootFieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureCorrespondence20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

theorem frontier (l : Fin 20) :
    DigestLift (PV_RunJoin_FixtureArguments.snapshot.frontier.val[l.val]!)
      (AspisR1.AppendNode.frozenEmpty (K := M) l.castSucc) := by
  have hf : digK (K := M) (PV_RunJoin_FixtureArguments.snapshot.frontier.val[l.val]!) =
      PV_RunJoin_RootModel.literal l.castSucc := by
    fin_cases l <;> funext i <;> fin_cases i <;> rfl
  rw [PV_RunJoin_RootModel.frozen_literal]
  exact congrFun hf
#print axioms frontier

theorem frontier_canon (l : Fin 20) : Canon8 (PV_RunJoin_FixtureArguments.snapshot.frontier.val[l.val]!) := by
  intro i hi
  fin_cases l <;> interval_cases i <;> decide
#print axioms frontier_canon

theorem empty (l : Fin 20) :
    (wordPublic transferPublic).empty.val[l.val]! = PV_Src_CanonicalRoots.table.val[l.val]! := by
  change (BuilderRecordsPublic.empty20 PV_Src_CanonicalRoots.table).val[l.val]! = _
  exact BuilderRecordsArray.tabulate_get _ _ _ (by simpa using l.isLt)
#print axioms empty

theorem transfer : PubCorr (wordPublic transferPublic) (PV_RunJoin_FixtureRecords.fixturePublic false) := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_,?_⟩
  · exact frontier
  · intro l
    change DigestLift ((wordPublic transferPublic).empty.val[l.val]!) _
    rw [empty]
    exact PV_Src_CanonicalRoots.meaning (K := M) l
  · exact frontier_canon
  · intro l
    change Canon8 ((wordPublic transferPublic).empty.val[l.val]!)
    rw [empty]
    exact PV_Src_CanonicalRoots.canonical l.castSucc
#print axioms transfer

theorem withdrawal : PubCorr (wordPublic withdrawalPublic) (PV_RunJoin_FixtureRecords.fixturePublic true) := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_,?_⟩
  · exact frontier
  · intro l
    change DigestLift ((wordPublic transferPublic).empty.val[l.val]!) _
    rw [empty]
    exact PV_Src_CanonicalRoots.meaning (K := M) l
  · exact frontier_canon
  · intro l
    change Canon8 ((wordPublic transferPublic).empty.val[l.val]!)
    rw [empty]
    exact PV_Src_CanonicalRoots.canonical l.castSucc
#print axioms withdrawal
end R1Z.PV_RunJoin_FixtureCorrespondence20
