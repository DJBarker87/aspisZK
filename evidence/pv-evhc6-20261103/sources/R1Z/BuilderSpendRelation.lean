import R1Z.BuilderSemanticBridge
import R0Z.BuilderModelRefines
import SpendRelation

/-! The D50 relation `Rspend⁺` implies the builder's semantic premises.
This identifies mathematical witnesses; it does not extract Rust's admission
checks, records function, public projection, or structural glue. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderSpendRelation
open R0P R0Z.BuilderModel R1Z.BuilderSemanticBridge
open AspisR1 AspisR1.SpendRelation AspisPool.V7PairLeafOccupancy
variable {K : Type} [Field K] [DecidableEq K] [CharP K 2147483647]
attribute [local irreducible] blockOut blockDigest poseidonPermutation

/-- The spend witness has exactly the fields read by the model. -/
def modelWitness (w : Witness K) : ModelWitness K where
  inputValue := w.inputValue
  outputValue := w.outputValue
  changeValue := w.changeValue
  sk := w.sk
  salt := w.salt
  path := w.path
  pairFirst := w.pair.firstCommitment
  pairOccupied := w.pair.secondOccupied
  pairSecond := w.pair.secondCommitment
  pairInverse := w.pair.secondOccupancyInverse
  recipientOwner := w.recipientOwner
  recipientSalt := w.recipientSalt
  changeOwner := w.changeOwner
  changeSalt := w.changeSalt

/-- Privacy's strengthened relation, as adopted in D50. -/
def RspendPlus (pub : Public K) (w : Witness K) : Prop :=
  Rspend pub w ∧ (pub.variant = .privateTransfer → pub.change 7 ≠ 0)

theorem aux_of_spend (pub : Public K) (w : Witness K) (h : RspendPlus pub w) :
    AuxPremises pub (modelWitness w) where
  conservation := h.1.2.2.1
  pairValid := by
    have hv := h.1.2.1.valid
    exact ⟨hv.1, sub_eq_zero.mpr hv.2.1, hv.2.2.1, hv.2.2.2⟩
  spendable := by
    have hs := h.1.2.1.spendable
    cases hb : (w.path 0).1
    · simp [dirK, modelWitness, hb]
    · have he : w.pair.secondOccupied = 1 := by
        simpa only [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied, hb, if_true] using hs
      simp [dirK, modelWitness, hb, he]
  changeSentinel := by
    intro hv
    rw [changeDigest_eq pub (modelWitness w)]
    change changeCommitment pub w 7 ≠ 0
    rw [← h.1.2.2.2.1]
    exact h.2 hv
  amount := by
    intro hv a ha
    have ho := h.1.2.2.2.2.1
    unfold variantOutput at ho
    rw [hv] at ho
    exact (Option.some.inj (ha.symm.trans ho))

/-- PairRight is forced by selection and the first path sibling, not assumed. -/
theorem pairRight_of_spend (pub : Public K) (w : Witness K) (h : Rspend pub w) :
    PairRight pub (modelWitness w) := by
  unfold PairRight
  rw [inputLeaf_eq pub (modelWitness w)]
  change w.pair.secondCommitment =
    (ordered (noteCommitment (ownerKey w.sk) (w.inputValue.val : K) pub.assetId w.salt)
      (w.path 0).2 (w.path 0).1).2
  rw [← h.2.1.commitment, h.2.1.sibling]
  cases hb : (w.path 0).1 <;> simp [ordered, PairLeaf.selectedCommitment]

/-- Append prefixes are the same recurrence with the same frozen roots. -/
theorem appCur_eq (pub : Public K) (w : ModelWitness K) (leaf : R0P.Digest K) (n : Nat) :
    appCur pub leaf n = AppendPath.pathPrefix pub leaf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [appCur, AppendPath.pathPrefix]
    split_ifs with hn
    · rw [appNode, nodeDigest_eq pub w, ih]
      cases hb : appBit pub n
      · have hz : digestBitZero pub ⟨n, hn⟩ := by
          simpa only [appBit, decide_eq_false_iff_not, ne_eq, not_not] using hb
        simp only [appSib, hb, Bool.false_eq_true, if_false, ordered,
          AppendPath.step, if_pos hz]
        rfl
      · have hz : ¬ digestBitZero pub ⟨n, hn⟩ := of_decide_eq_true hb
        simp only [appSib, hb, if_true, ordered,
          AppendPath.step, if_neg hz]
    · exact ih

/-- The output-pair binding follows from the variant and public commitments. -/
theorem outputPair_eq (pub : Public K) (w : Witness K) (h : Rspend pub w) :
    outputPair pub = some (outPair pub (modelWitness w)) := by
  have hchange := h.2.2.2.1
  have hout := h.2.2.2.2.1
  cases hv : pub.variant
  · unfold variantOutput at hout
    rw [hv] at hout
    unfold outputPair outPair outPairB
    rw [hv, hout, Option.map_some, nodeDigest_eq pub (modelWitness w),
      recipientDigest_eq pub (modelWitness w) hv, changeDigest_eq pub (modelWitness w)]
    rw [hchange]
    rfl
  · unfold outputPair outPair outPairB
    rw [hv, nodeDigest_eq pub (modelWitness w), changeDigest_eq pub (modelWitness w), hchange]
    rfl

/-- Every public digest premise is derived from Rspend, including the carry. -/
theorem digest_of_spend (pub : Public K) (w : Witness K) (h : Rspend pub w) :
    DigestPremises pub (modelWitness w) where
  anchor := by
    rw [treeCur_eq pub (modelWitness w), inputLeaf_eq pub (modelWitness w)]
    exact h.2.1.membership
  nullifier := by
    rw [nullifierDigest_eq pub (modelWitness w)]
    exact h.2.1.nullifier
  recipient := by
    intro r hr
    cases hv : pub.variant
    · have ho := h.2.2.2.2.1
      unfold variantOutput at ho
      rw [hv] at ho
      rw [recipientDigest_eq pub (modelWitness w) hv]
      exact Option.some.inj (hr.symm.trans ho)
    · obtain ⟨a, ha, haw, hnone⟩ := PublicOptionShape.withdrawal_shape pub hv h.1
      rw [hnone] at hr
      contradiction
  change := by
    rw [changeDigest_eq pub (modelWitness w)]
    exact h.2.2.2.1
  nextRoot := by
    obtain ⟨pair, hp, hr, hc⟩ := h.2.2.2.2.2
    rw [outputPair_eq pub w h] at hp
    have he := Option.some.inj hp
    rw [← he, ← appCur_eq pub (modelWitness w)] at hr
    exact hr
  carry := by
    intro hc
    obtain ⟨pair, hp, hr, hcarry⟩ := h.2.2.2.2.2
    rw [outputPair_eq pub w h] at hp
    have he := Option.some.inj hp
    rw [appCur_eq pub (modelWitness w), he]
    exact hcarry hc

/-- T4 at the semantic boundary: the D51 premises follow from Rspend⁺ and
base-field membership; no auxiliary/digest/PairRight hypothesis remains. -/
theorem modelRel_of_spend [Fintype K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (F : Subfield K) (pub : Public K) (w : Witness K)
    (hp : PublicBase F pub) (hw : WitnessBase F (modelWitness w))
    (h : RspendPlus pub w) : ModelRel F pub (modelWitness w) :=
  ⟨hp, hw, aux_of_spend pub w h, digest_of_spend pub w h.1, pairRight_of_spend pub w h.1⟩

#print axioms aux_of_spend
#print axioms pairRight_of_spend
#print axioms appCur_eq
#print axioms outputPair_eq
#print axioms digest_of_spend
#print axioms modelRel_of_spend
end R1Z.BuilderSpendRelation
