import R1InputWitnessRelationCore
import R1SpendAppendBindingCore
import PublicOptionShape
import AspisV8R15.ExactTowerBase

/-! An explicit witness and decidable semantic spend relation. The concrete
witness field is M31; the generic version supports the existing algebraic
extraction proofs. This is not a byte parser or a Rust refinement theorem.
Values are bounded nonnegative integers, as in the production value theorem;
the honest pair-forest builder's stronger positivity contract is separate. -/
set_option autoImplicit false
namespace AspisR1.SpendRelation

open R0P AspisPool.V7PairLeafOccupancy

structure Witness (K : Type) where
  inputValue : Fin (2^30)
  outputValue : Fin (2^30)
  changeValue : Fin (2^30)
  sk : R0P.Digest K
  salt : R0P.Digest K
  path : Fin 24 → Bool × R0P.Digest K
  pair : PairLeaf K
  recipientOwner : R0P.Digest K
  recipientSalt : R0P.Digest K
  changeOwner : R0P.Digest K
  changeSalt : R0P.Digest K

variable {K : Type} [Field K] [DecidableEq K]

def recipientCommitment (pub : Public K) (w : Witness K) : R0P.Digest K :=
  noteCommitment w.recipientOwner (w.outputValue.val : K) pub.assetId w.recipientSalt

def changeCommitment (pub : Public K) (w : Witness K) : R0P.Digest K :=
  noteCommitment w.changeOwner (w.changeValue.val : K) pub.assetId w.changeSalt

def variantOutput (pub : Public K) (w : Witness K) : Prop :=
  match pub.variant with
  | .privateTransfer => pub.recipient = some (recipientCommitment pub w)
  | .withdrawal => pub.withdrawalAmount = some (w.outputValue.val : K)

def Rspend (pub : Public K) (w : Witness K) : Prop :=
  PublicOptionShape.canonical pub ∧
    InputWitnessCore.Relation pub (w.inputValue.val : K) w.sk w.salt w.path w.pair ∧
    w.inputValue.val = w.outputValue.val + w.changeValue.val ∧
    pub.change = changeCommitment pub w ∧
    variantOutput pub w ∧ AppendBinding pub

abbrev Wspend := Witness AspisV8R15.ExactTowerBase.M31Exact

end AspisR1.SpendRelation


set_option pp.universes true in
#check @AspisR1.SpendRelation.Witness

#print AspisR1.SpendRelation.Witness
#print axioms AspisR1.SpendRelation.Witness

#print AspisR1.SpendRelation.recipientCommitment
#print axioms AspisR1.SpendRelation.recipientCommitment

#print AspisR1.SpendRelation.changeCommitment
#print axioms AspisR1.SpendRelation.changeCommitment

#print AspisR1.SpendRelation.variantOutput
#print axioms AspisR1.SpendRelation.variantOutput

#print AspisR1.SpendRelation.Rspend
#print axioms AspisR1.SpendRelation.Rspend

#print AspisR1.SpendRelation.Wspend
#print axioms AspisR1.SpendRelation.Wspend
