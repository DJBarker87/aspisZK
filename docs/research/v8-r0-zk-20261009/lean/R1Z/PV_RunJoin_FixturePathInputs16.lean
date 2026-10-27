import R1Z.PV_RunJoin_TreeLift16
import R1Z.PV_RunJoin_InputLeaf16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixturePathInputs16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M
abbrev transferW := PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness
abbrev withdrawalW := PV_Src_Forest_PrimitiveArguments.wordWitness withdrawalWitness

theorem transfer_path : (toModel (K := M) transferW).path = PV_RunJoin_FixtureRecords.path := by
  funext l
  apply Prod.ext
  · fin_cases l <;> decide
  · fin_cases l <;> funext i <;> fin_cases i <;> rfl

theorem transfer_leaf : inputLeaf (PV_RunJoin_FixtureRecords.base false) (toModel (K := M) transferW) =
    R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23 := by
  rw [BuilderSemanticBridge.inputLeaf_eq]
  have sk : (toModel (K := M) transferW).sk = PV_RunJoin_FixtureRecords.digest 10 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) transferW).salt = PV_RunJoin_FixtureRecords.digest 100 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) transferW).inputValue.val = 1000 := rfl
  rw [sk,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl]
  simp only [Nat.cast_ofNat]
  exact PV_RunJoin_FixtureHashModel.input_commitment

theorem transfer_tree (n : Nat) :
    treeCur (toModel (K := M) transferW)
      (inputLeaf (PV_RunJoin_FixtureRecords.base false) (toModel (K := M) transferW)) n =
      R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23) PV_RunJoin_FixtureRecords.path n := by
  rw [BuilderSemanticBridge.treeCur_eq (PV_RunJoin_FixtureRecords.base false),transfer_leaf,transfer_path]
#print axioms transfer_path
#print axioms transfer_leaf
#print axioms transfer_tree

theorem withdrawal_path : (toModel (K := M) withdrawalW).path = PV_RunJoin_FixtureRecords.path := by
  funext l
  apply Prod.ext
  · fin_cases l <;> decide
  · fin_cases l <;> funext i <;> fin_cases i <;> rfl

theorem withdrawal_leaf : inputLeaf (PV_RunJoin_FixtureRecords.base false) (toModel (K := M) withdrawalW) =
    R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23 := by
  rw [BuilderSemanticBridge.inputLeaf_eq]
  have sk : (toModel (K := M) withdrawalW).sk = PV_RunJoin_FixtureRecords.digest 10 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) withdrawalW).salt = PV_RunJoin_FixtureRecords.digest 100 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) withdrawalW).inputValue.val = 1000 := rfl
  rw [sk,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl]
  simp only [Nat.cast_ofNat]
  exact PV_RunJoin_FixtureHashModel.input_commitment

theorem withdrawal_tree (n : Nat) :
    treeCur (toModel (K := M) withdrawalW)
      (inputLeaf (PV_RunJoin_FixtureRecords.base false) (toModel (K := M) withdrawalW)) n =
      R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23) PV_RunJoin_FixtureRecords.path n := by
  rw [BuilderSemanticBridge.treeCur_eq (PV_RunJoin_FixtureRecords.base false),withdrawal_leaf,withdrawal_path]
#print axioms withdrawal_path
#print axioms withdrawal_leaf
#print axioms withdrawal_tree
end R1Z.PV_RunJoin_FixturePathInputs16
