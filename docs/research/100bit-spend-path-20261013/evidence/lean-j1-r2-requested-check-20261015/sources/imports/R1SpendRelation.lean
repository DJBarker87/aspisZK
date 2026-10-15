import R1InputWitnessCheck
import PublicOptionShape
import AspisV8R15.ExactTowerBase
import R1SpendAppendBinding

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

def variantOutputCheck (pub : Public K) (w : Witness K) : Bool :=
  match pub.variant with
  | .privateTransfer =>
      match pub.recipient with
      | none => false
      | some recipient => InputWitnessCheck.digestEqCheck recipient (recipientCommitment pub w)
  | .withdrawal =>
      match pub.withdrawalAmount with
      | none => false
      | some amount => decide (amount = (w.outputValue.val : K))

def check (pub : Public K) (w : Witness K) : Bool :=
  PublicOptionShape.check pub &&
    InputWitnessCheck.check pub (w.inputValue.val : K) w.sk w.salt w.path w.pair &&
    decide (w.inputValue.val = w.outputValue.val + w.changeValue.val) &&
    InputWitnessCheck.digestEqCheck pub.change (changeCommitment pub w) &&
    variantOutputCheck pub w && appendCheck pub

/-- The concrete relation uses canonical M31 field elements for every key,
salt, path digest, pair coordinate and output owner. -/
abbrev Wspend := Witness AspisV8R15.ExactTowerBase.M31Exact

def checkM31 (pub : Public AspisV8R15.ExactTowerBase.M31Exact) (w : Wspend) : Bool :=
  check pub w

theorem variantOutputCheck_eq_true_iff (pub : Public K) (w : Witness K) :
    variantOutputCheck pub w = true ↔ variantOutput pub w := by
  cases hv : pub.variant with
  | privateTransfer =>
      cases hr : pub.recipient <;>
        simp [variantOutputCheck, variantOutput, hv, hr,
          InputWitnessCheck.digestEqCheck_eq_true_iff]
  | withdrawal =>
      cases ha : pub.withdrawalAmount <;>
        simp [variantOutputCheck, variantOutput, hv, ha]

theorem check_eq_true_iff (pub : Public K) (w : Witness K) :
    check pub w = true ↔ Rspend pub w := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    PublicOptionShape.check_eq_true_iff, InputWitnessCheck.check_eq_true_iff,
    InputWitnessCheck.digestEqCheck_eq_true_iff, variantOutputCheck_eq_true_iff,
    appendCheck_eq_true_iff, Rspend, and_assoc]

theorem input_note_extracted (pub : Public K) (w : Witness K) (A : Trace K)
    (hvalue : A 10 1008 = (w.inputValue.val : K)) (h : Rspend pub w) :
    R0P.InputNoteExtracted pub A := by
  refine ⟨w.sk, w.salt, w.path, h.2.1.nullifier, ?_⟩
  rw [hvalue]
  exact h.2.1.membership

theorem integer_bounds (pub : Public K) (w : Witness K) (h : Rspend pub w) :
    w.inputValue.val < 2^30 ∧ w.outputValue.val < 2^30 ∧ w.changeValue.val < 2^30 ∧
      w.inputValue.val = w.outputValue.val + w.changeValue.val :=
  ⟨w.inputValue.isLt, w.outputValue.isLt, w.changeValue.isLt, h.2.2.1⟩

#print axioms input_note_extracted
#print axioms integer_bounds
#print axioms variantOutputCheck_eq_true_iff
#print axioms check_eq_true_iff
end AspisR1.SpendRelation
