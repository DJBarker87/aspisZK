import R0Z.BuilderModelHash
import R0P.Digest

/-! Builder model, public digest binding (t2b2b/DESIGN-BUILDER-MODEL.txt §4).
`digestFamily` holds on the model under `DigestPremises`: the public anchor,
nullifier, recipient, change, next root and carry frontier equal the digests
the model computes (the equality checks the Rust builder performs before it
returns, pair_trace.rs:632-662, 593-595, pair_forest_trace.rs:241-243, plus
the afterstate it publishes).  The frozen empty-root lanes and the snapshot
frontier lanes hold by construction; the last empty-root limb needs
characteristic 2^31−1 (M31 add before the lift, EmptyRoots.lean). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

theorem blockCell_11 (b : BlockIn K) (i : Fin 8) (h : i.val < 16) :
    blockCell b 11 ⟨i.val, h⟩ = blockDigest b i := rfl

theorem blockCell_12 (b : BlockIn K) (c : Fin 16) : blockCell b 12 c = b.absorb c := rfl

theorem treeCur_succ (w : ModelWitness K) (leaf : Digest K) (n : Nat) (hn : n < 24) :
    treeCur w leaf (n + 1) = blockDigest (treeNode w (treeCur w leaf n) ⟨n, hn⟩) := by
  rw [treeCur.eq_2, dif_pos hn]

theorem appCur_succ (pub : Public K) (start : Digest K) (n : Nat) (hn : n < 20) :
    appCur pub start (n + 1) = blockDigest (appNode pub (appCur pub start n) ⟨n, hn⟩) := by
  rw [appCur.eq_2, dif_pos hn]

theorem appCur_zero (pub : Public K) (start : Digest K) : appCur pub start 0 = start := by
  rw [appCur.eq_1]

attribute [local irreducible] blockOut blockIter blockDigest treeCur appCur

theorem digest_cell (C : Cells K) (h : Fin 57) (r : Fin 1024) (hr : r.val = 16 * h.val + 11)
    (i : Fin 8) : layout C (i.castAdd 21) r = blockDigest (C.blocks h) i := by
  rw [layout_block' C _ (lt_of_lt_of_le i.isLt (by norm_num)) h 11 (by norm_num) r hr]
  exact blockCell_11 _ i _

theorem blocksOf_app' (pub : Public K) (w : ModelWitness K) (h : Fin 57) (j : Nat)
    (hj : h.val = 34 + j) (hj20 : j < 20) :
    blocksOf pub w h = appNode pub (appCur pub (outPair pub w) j) ⟨j, hj20⟩ := by
  rw [blocksOf_app pub w h (by omega) (by omega)]
  have e : (⟨h.val - 34, by omega⟩ : Fin 20) = ⟨j, hj20⟩ := Fin.ext (by simp; omega)
  rw [e, show h.val - 34 = j by omega]

theorem m31_lift [CharP K 0x7fffffff] (s : Nat) :
    (((if s ≥ 0x7fffffff then s - 0x7fffffff else s : Nat)) : K) = (s : K) := by
  split_ifs with h
  · rw [Nat.cast_sub h, CharP.cast_eq_zero K 0x7fffffff, sub_zero]
  · rfl

theorem emptyRootK_congr (l : Fin 20) (a b : Fin 8) (h : a.val = b.val) :
    emptyRootK (K := K) l a = emptyRootK l b := by
  rw [Fin.ext h]

/-- A zero append bit puts the frozen empty root (with the M31-added tweak on
the last limb) in lanes 8..15 of the node's pre-state. -/
theorem app_pre_zero [CharP K 0x7fffffff] (pub : Public K) (cur : Digest K) (l : Fin 20)
    (hb : appBit pub l.val = false) (i : Fin 8) (hc : 8 + i.val < 16) :
    (appNode pub cur l).pre ⟨8 + i.val, hc⟩ = emptyRootRightTarget l i := by
  unfold appNode appSib ordered nodeIn
  simp only [hb, Bool.false_eq_true, if_false]
  rw [if_neg (show ¬ ((⟨8 + i.val, hc⟩ : Fin 16).val < 8) by simp)]
  unfold emptyRootRightTarget
  by_cases hi : i.val = 7
  · rw [if_pos (show (⟨8 + i.val, hc⟩ : Fin 16).val = 15 by simp; omega),
      if_pos (show i.val + 1 = 8 by omega)]
    have hi7 : i = 7 := Fin.ext hi
    subst hi7
    dsimp only
    rw [m31_lift, Nat.cast_add, Nat.cast_ofNat]
    rfl
  · rw [if_neg (show ¬ ((⟨8 + i.val, hc⟩ : Fin 16).val = 15) by simp; omega),
      if_neg (show ¬ (i.val + 1 = 8) by omega)]
    exact emptyRootK_congr l _ i (by simp)

/-- A one append bit puts the snapshot frontier in the absorbed left child. -/
theorem app_absorb_one (pub : Public K) (cur : Digest K) (l : Fin 20)
    (hb : appBit pub l.val = true) (i : Fin 8) (hc : i.val < 16) :
    (appNode pub cur l).absorb ⟨i.val, hc⟩ = pub.snapshotFrontier l i := by
  unfold appNode appSib ordered nodeIn lo8
  simp only [hb, if_true]
  rw [dif_pos i.isLt]

/-- The witness-side premises of the digest family. -/
structure DigestPremises (pub : Public K) (w : ModelWitness K) : Prop where
  anchor : pub.anchor = treeCur w (inputLeaf pub w) 24
  nullifier : pub.nullifier = nullifierDigest w
  recipient : ∀ r, pub.recipient = some r → r = recipientDigest pub w
  change : pub.change = changeDigest pub w
  nextRoot : pub.nextRoot = appCur pub (outPair pub w) 20
  carry : ∀ hc : digestCarry pub.nextPairIndex < 20,
    pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩ =
      appCur pub (outPair pub w) (digestCarry pub.nextPairIndex)

theorem blocksOf_carry (pub : Public K) (w : ModelWitness K) (k : Nat) (hk : k < 20) :
    blockDigest (blocksOf pub w ⟨33 + k, by omega⟩) = appCur pub (outPair pub w) k := by
  cases k with
  | zero =>
      rw [appCur_zero]
      show blockDigest (outPairB pub w) = outPair pub w
      rfl
  | succ j =>
      rw [blocksOf_app' pub w _ j (by simp; omega) (by omega), appCur_succ pub _ j (by omega)]

theorem digest_model [CharP K 0x7fffffff] (pub : Public K) (w : ModelWitness K)
    (hP : DigestPremises pub w) : Holds digestFamily pub (buildModel pub w) := by
  rw [digest_holds_iff]
  refine ⟨fun i => ?_, fun i => ?_, fun r hr i => ?_, fun i => ?_, fun level => ⟨fun hz i => ?_,
    fun hnz i => ?_⟩, fun i => ?_, fun hc i => ?_⟩
  · rw [buildModel, digest_cell _ 56 907 rfl i, hP.anchor]
    show blockDigest (treeNode w (treeCur w (inputLeaf pub w) 23) ⟨23, by decide⟩) i = _
    exact congrFun (treeCur_succ w _ 23 (by decide)).symm i
  · rw [buildModel, digest_cell _ 26 427 rfl i, hP.nullifier]
    rfl
  · rw [buildModel, digest_cell _ 29 475 rfl i, hP.recipient r hr]
    rfl
  · rw [buildModel, digest_cell _ 32 523 rfl i, hP.change]
    rfl
  · have hb : appBit pub level.val = false := decide_eq_false (fun h => h hz)
    rw [buildModel, layout_block' _ _ (by simp; omega) ⟨34 + level.val, by omega⟩ 0 (by decide) _
      (by simp [g2Row]), blockCell_pre]
    show (blocksOf pub w ⟨34 + level.val, by omega⟩).pre _ = _
    rw [blocksOf_app' pub w _ level.val rfl level.isLt]
    exact app_pre_zero pub _ level hb i _
  · have hb : appBit pub level.val = true := decide_eq_true hnz
    rw [buildModel, layout_block' _ _ (lt_of_lt_of_le i.isLt (by norm_num)) ⟨34 + level.val, by omega⟩
      12 (by decide) _ (by simp [g2Row]), blockCell_12]
    show (blocksOf pub w ⟨34 + level.val, by omega⟩).absorb _ = _
    rw [blocksOf_app' pub w _ level.val rfl level.isLt]
    exact app_absorb_one pub _ level hb i _
  · rw [buildModel, digest_cell _ 53 859 rfl i, hP.nextRoot]
    show blockDigest (appNode pub (appCur pub (outPair pub w) 19) ⟨19, by decide⟩) i = _
    exact congrFun (appCur_succ pub _ 19 (by decide)).symm i
  · rw [buildModel, digest_cell _ ⟨33 + digestCarry pub.nextPairIndex, by omega⟩ _
      (by simp [g2Row]) i, hP.carry hc]
    exact congrFun (blocksOf_carry pub w _ hc) i

#print axioms treeCur_succ
#print axioms appCur_succ
#print axioms digest_cell
#print axioms blocksOf_app'
#print axioms m31_lift
#print axioms app_pre_zero
#print axioms app_absorb_one
#print axioms blocksOf_carry
#print axioms digest_model
end R0Z.BuilderModel
