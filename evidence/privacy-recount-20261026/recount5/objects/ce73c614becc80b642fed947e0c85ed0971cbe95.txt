import R0Z.BuilderModelAux
import R0Z.BuilderModelDigest
import R0P.PositivityChain

/-! Copy-link kinds for the builder model (t2b2b/DESIGN-BUILDER-MODEL.txt §4 a).

The 136 links of R0P `copyLinks` fall into a few kinds.  This module proves
one symbolic cell lemma per kind, parametrised by the level / block, plus the
handful of one-off cell facts; `BuilderModelCopyPat` (generated) proves the
pattern-pair lemmas and `BuilderModelCopyLinks*` (generated) apply them link
by link.  No cell is evaluated: every lemma rewrites through the block-role
and aux-row lemmas with the heavy definitions irreducible. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

/-! ### Link plumbing -/

/-- The 16 trace cells of row `r` an endpoint pattern reads. -/
def rv (A : Trace K) (r : Fin 1024) : Fin 16 → K := fun c => A (Fin.castLE (by omega) c) r

theorem link_of (A : Trace K) (L : CopyLink)
    (h : copyPatternTuple (copyPatterns L.producer.pattern) (rv A L.producer.row) =
      copyPatternTuple (copyPatterns L.consumer.pattern) (rv A L.consumer.row)) :
    copyProducerTuple A L = copyConsumerTuple A L :=
  Prod.ext rfl h

theorem w1_variant (L : CopyLink) (idx : Nat) (v : Variant) (hk : L.weightKind.val = 1)
    (hw : copyLinkWeight (K := K) L idx v ≠ 0) : v = .privateTransfer := by
  unfold copyLinkWeight at hw
  rw [hk] at hw
  by_contra hv
  exact hw (if_neg hv)

theorem w2_variant (L : CopyLink) (idx : Nat) (v : Variant) (hk : L.weightKind.val = 2)
    (hw : copyLinkWeight (K := K) L idx v ≠ 0) : v = .withdrawal := by
  unfold copyLinkWeight at hw
  rw [hk] at hw
  by_contra hv
  exact hw (if_neg hv)

theorem bit_le_one (x : Nat) : (x &&& 1) ≤ 1 := by
  rw [Nat.and_one_is_mod]; omega

theorem w3_bit (L : CopyLink) (idx : Nat) (v : Variant) (hk : L.weightKind.val = 3)
    (hw : copyLinkWeight (K := K) L idx v ≠ 0) : (idx >>> L.weightLevel &&& 1) = 0 := by
  unfold copyLinkWeight at hw
  rw [hk] at hw
  have hb := bit_le_one (idx >>> L.weightLevel)
  by_contra hne
  have h1 : (idx >>> L.weightLevel &&& 1) = 1 := by omega
  exact hw (by simp only [h1, Nat.sub_self, Nat.cast_zero])

theorem w4_bit (L : CopyLink) (idx : Nat) (v : Variant) (hk : L.weightKind.val = 4)
    (hw : copyLinkWeight (K := K) L idx v ≠ 0) : (idx >>> L.weightLevel &&& 1) ≠ 0 := by
  unfold copyLinkWeight at hw
  rw [hk] at hw
  intro h0
  exact hw (by simp only [h0, Nat.cast_zero])

theorem appBit_false (pub : Public K) (l : Nat) (h : (pub.nextPairIndex >>> l &&& 1) = 0) :
    appBit pub l = false := decide_eq_false (fun hn => hn h)

theorem appBit_true (pub : Public K) (l : Nat) (h : (pub.nextPairIndex >>> l &&& 1) ≠ 0) :
    appBit pub l = true := decide_eq_true h

/-! ### Node and tweak facts -/

theorem nodeIn_absorb (l r : Digest K) (i : Fin 8) :
    (nodeIn l r).absorb ⟨i.val, by omega⟩ = l i := by
  show lo8 l ⟨i.val, _⟩ = l i
  unfold lo8
  rw [dif_pos i.isLt]

theorem nodeIn_pre_lt7 (l r : Digest K) (i : Fin 8) (hi : i.val < 7) :
    (nodeIn l r).pre ⟨8 + i.val, by omega⟩ = r i := by
  show (if (8 + i.val) < 8 then 0 else if 8 + i.val = 15 then r 7 + (0x4153_1005 : K)
    else r ⟨8 + i.val - 8, _⟩) = r i
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  exact Fin.ext (by simp)

theorem nodeIn_pre_15 (l r : Digest K) : (nodeIn l r).pre 15 = r 7 + (0x4153_1005 : K) := rfl

theorem tweak_cancel [CharP K 0x7fffffff] (x : K) :
    x + (0x4153_1005 : K) + ((1051521018 : Nat) : K) = x := by
  rw [add_assoc]
  have h : (0x4153_1005 : K) + ((1051521018 : Nat) : K) = ((0x7fffffff : Nat) : K) := by
    push_cast; norm_num
  rw [h, CharP.cast_eq_zero K 0x7fffffff, add_zero]

/-! ### Layout cell access -/

theorem cell_block (C : Cells K) (c : Fin 29) (hc : c.val < 16) (h : Fin 57) (l : Nat) (hl : l < 16)
    (r : Fin 1024) (hr : r.val = 16 * h.val + l) :
    layout C c r = blockCell (C.blocks h) l ⟨c.val, hc⟩ := layout_block' C c hc h l hl r hr

theorem cell_aux (C : Cells K) (c : Fin 29) (hc : c.val < 16) (r : Fin 1024)
    (hr : 57 ≤ r.val / 16) : layout C c r = auxCell C r.val ⟨c.val, hc⟩ := layout_aux C c r hc hr

/-! ### Membership levels: rows and blocks -/

/-- Block holding the membership node of level l (FH membership_hash_block). -/
def nodeBlock (l : Fin 24) : Nat := if l.val ≤ 20 then 4 + l.val else 33 + l.val

/-- Block whose output is level l's current digest (block 3 = input leaf). -/
def prevBlock (l : Fin 24) : Nat := if l.val = 0 then 3 else if l.val ≤ 21 then 3 + l.val else 32 + l.val

/-- Path aux base row of level l (pool_v1_pair_forest_path_base_row_v1). -/
def pathBase (l : Fin 24) : Nat := 912 + 16 * (l.val / 4) + 1 + 4 * (l.val % 4)

theorem nodeBlock_lt (l : Fin 24) : nodeBlock l < 57 := by
  have := l.isLt; unfold nodeBlock; split <;> omega

theorem prevBlock_lt (l : Fin 24) : prevBlock l < 57 := by
  have := l.isLt; unfold prevBlock; split
  · omega
  · split <;> omega

theorem pathBase_lt (l : Fin 24) : pathBase l + 1 < 1024 := by
  have := l.isLt; unfold pathBase; omega

attribute [local irreducible] blockOut blockIter blockDigest treeCur appCur

theorem blocksOf_node' (pub : Public K) (w : ModelWitness K) (l : Fin 24) :
    blocksOf pub w ⟨nodeBlock l, nodeBlock_lt l⟩ =
      treeNode w (treeCur w (inputLeaf pub w) l.val) l := by
  have hl := l.isLt
  by_cases h20 : l.val ≤ 20
  · have hv : nodeBlock l = 4 + l.val := by unfold nodeBlock; rw [if_pos h20]
    rw [blocksOf_tree_lo pub w _ (show 4 ≤ nodeBlock l by omega) (show nodeBlock l ≤ 24 by omega)]
    have e : (⟨(⟨nodeBlock l, nodeBlock_lt l⟩ : Fin 57).val - 4, by
        show nodeBlock l - 4 < 24; omega⟩ : Fin 24) = l :=
      Fin.ext (show nodeBlock l - 4 = l.val by omega)
    rw [e, show (⟨nodeBlock l, nodeBlock_lt l⟩ : Fin 57).val - 4 = l.val from
      (show nodeBlock l - 4 = l.val by omega)]
  · have hv : nodeBlock l = 33 + l.val := by unfold nodeBlock; rw [if_neg h20]
    rw [blocksOf_tree_hi pub w _ (show 54 ≤ nodeBlock l by omega)]
    have e : (⟨(⟨nodeBlock l, nodeBlock_lt l⟩ : Fin 57).val - 33, by
        show nodeBlock l - 33 < 24; omega⟩ : Fin 24) = l :=
      Fin.ext (show nodeBlock l - 33 = l.val by omega)
    rw [e, show (⟨nodeBlock l, nodeBlock_lt l⟩ : Fin 57).val - 33 = l.val from
      (show nodeBlock l - 33 = l.val by omega)]

theorem prevBlock_digest (pub : Public K) (w : ModelWitness K) (l : Fin 24) :
    blockDigest (blocksOf pub w ⟨prevBlock l, prevBlock_lt l⟩) =
      treeCur w (inputLeaf pub w) l.val := by
  have hl := l.isLt
  by_cases h0 : l.val = 0
  · have e : (⟨prevBlock l, prevBlock_lt l⟩ : Fin 57) = 3 :=
      Fin.ext (by show prevBlock l = 3; unfold prevBlock; rw [if_pos h0])
    rw [e, h0, treeCur.eq_1]
    rfl
  · obtain ⟨k, hk⟩ : ∃ k, l.val = k + 1 := ⟨l.val - 1, by omega⟩
    have e : (⟨prevBlock l, prevBlock_lt l⟩ : Fin 57) = ⟨nodeBlock ⟨k, by omega⟩, nodeBlock_lt _⟩ :=
      Fin.ext (by
        show prevBlock l = nodeBlock ⟨k, _⟩
        unfold prevBlock nodeBlock
        rw [if_neg h0]
        split <;> split <;> simp only [] at * <;> omega)
    rw [e, blocksOf_node', hk, treeCur_succ w _ k (by omega)]

/-! ### Path kinds (72 links) -/

theorem pathBase_aux (C : Cells K) (l : Fin 24) (c : Fin 16) :
    auxCell C (pathBase l) c = pathBaseCell (C.path l) c := by
  have hl := l.isLt
  unfold auxCell
  rw [dif_pos (show 912 ≤ pathBase l ∧ pathBase l < 1008 by unfold pathBase; omega),
    if_pos (show pathBase l % 16 % 4 = 1 by unfold pathBase; omega)]
  exact congrArg (fun p : Fin 24 => pathBaseCell (C.path p) c)
    (Fin.ext (show 4 * ((pathBase l - 912) / 16) + pathBase l % 16 / 4 = l.val by
      unfold pathBase; omega))

theorem pathSucc_aux (C : Cells K) (l : Fin 24) (c : Fin 16) :
    auxCell C (pathBase l + 1) c = pathSuccCell (C.path l) c := by
  have hl := l.isLt
  unfold auxCell
  rw [dif_pos (show 912 ≤ pathBase l + 1 ∧ pathBase l + 1 < 1008 by unfold pathBase; omega),
    if_neg (show ¬ ((pathBase l + 1) % 16 % 4 = 1) by unfold pathBase; omega),
    if_pos (show (pathBase l + 1) % 16 % 4 = 2 by unfold pathBase; omega)]
  exact congrArg (fun p : Fin 24 => pathSuccCell (C.path p) c)
    (Fin.ext (show 4 * ((pathBase l + 1 - 912) / 16) + (pathBase l + 1) % 16 / 4 = l.val by
      unfold pathBase; omega))

section model
variable (pub : Public K) (w : ModelWitness K)

/-- Path current: digest of the previous block = path base row columns 1..8. -/
theorem pathCur_cell (l : Fin 24) (i : Fin 8) :
    buildModel pub w (i.castAdd 21) ⟨16 * prevBlock l + 11, by have := prevBlock_lt l; omega⟩ =
      buildModel pub w ⟨1 + i.val, by omega⟩ ⟨pathBase l, by have := pathBase_lt l; omega⟩ := by
  have hl := l.isLt
  rw [buildModel, digest_cell _ ⟨prevBlock l, prevBlock_lt l⟩ _ rfl i,
    cell_aux _ _ (by simp only []; omega) _ (by show 57 ≤ pathBase l / 16; unfold pathBase; omega)]
  show blockDigest (blocksOf pub w _) i = auxCell _ (pathBase l) _
  rw [pathBase_aux, prevBlock_digest, pathBaseCell_cur _ _ i (by simp only []; omega)]
  rfl

/-- Path left: successor row columns 0..7 = node block row 12 (absorbed left). -/
theorem pathLeft_cell (l : Fin 24) (i : Fin 8) :
    buildModel pub w ⟨i.val, by omega⟩ ⟨pathBase l + 1, pathBase_lt l⟩ =
      buildModel pub w ⟨i.val, by omega⟩ ⟨16 * nodeBlock l + 12, by have := nodeBlock_lt l; omega⟩ := by
  have hl := l.isLt
  rw [buildModel, cell_aux _ _ (by simp only []; omega) _
      (by show 57 ≤ (pathBase l + 1) / 16; unfold pathBase; omega),
    cell_block _ _ (by simp only []; omega) ⟨nodeBlock l, nodeBlock_lt l⟩ 12 (by decide) _ rfl]
  show auxCell _ (pathBase l + 1) _ = blockCell (blocksOf pub w _) 12 _
  rw [pathSucc_aux, blocksOf_node', blockCell_12, pathSuccCell_left _ _ i rfl]
  exact (nodeIn_absorb _ _ i).symm

/-- Path right, lanes 0..6: successor columns 8..14 = node pre-state lanes 8..14. -/
theorem pathRight_cell (l : Fin 24) (i : Fin 8) (hi : i.val < 7) :
    buildModel pub w ⟨8 + i.val, by omega⟩ ⟨pathBase l + 1, pathBase_lt l⟩ =
      buildModel pub w ⟨8 + i.val, by omega⟩ ⟨16 * nodeBlock l, by have := nodeBlock_lt l; omega⟩ := by
  have hl := l.isLt
  rw [buildModel, cell_aux _ _ (by simp only []; omega) _
      (by show 57 ≤ (pathBase l + 1) / 16; unfold pathBase; omega),
    cell_block _ _ (by simp only []; omega) ⟨nodeBlock l, nodeBlock_lt l⟩ 0 (by decide) _ (by simp)]
  show auxCell _ (pathBase l + 1) _ = blockCell (blocksOf pub w _) 0 _
  rw [pathSucc_aux, blocksOf_node', blockCell_pre, pathSuccCell_right _ _ i rfl]
  exact (nodeIn_pre_lt7 _ _ i hi).symm

/-- Path right, lane 7: the node pre-state carries the tweak, removed by the
consumer offset 1051521018 = p − 0x41531005. -/
theorem pathRight7_cell [CharP K 0x7fffffff] (l : Fin 24) :
    buildModel pub w 15 ⟨pathBase l + 1, pathBase_lt l⟩ =
      buildModel pub w 15 ⟨16 * nodeBlock l, by have := nodeBlock_lt l; omega⟩ +
        ((1051521018 : Nat) : K) := by
  have hl := l.isLt
  rw [buildModel, cell_aux _ _ (by decide) _
      (by show 57 ≤ (pathBase l + 1) / 16; unfold pathBase; omega),
    cell_block _ _ (by decide) ⟨nodeBlock l, nodeBlock_lt l⟩ 0 (by decide) _ (by simp)]
  show auxCell _ (pathBase l + 1) 15 = blockCell (blocksOf pub w _) 0 15 + _
  rw [pathSucc_aux, blocksOf_node', blockCell_pre, pathSuccCell_right _ _ 7 rfl]
  unfold treeNode
  rw [nodeIn_pre_15, tweak_cancel]
  rfl

/-! ### Append kinds (40 links) -/

theorem app_digest (j : Nat) (hj : j < 20) :
    blockDigest (blocksOf pub w ⟨33 + j, by omega⟩) = appCur pub (outPair pub w) j :=
  blocksOf_carry pub w j hj

/-- Append, bit 0: block 33+j's digest is the left child absorbed by block 34+j. -/
theorem appLeft_cell (j : Nat) (hj : j < 20) (hb : appBit pub j = false) (i : Fin 8) :
    buildModel pub w (i.castAdd 21) ⟨16 * (33 + j) + 11, by omega⟩ =
      buildModel pub w ⟨i.val, by omega⟩ ⟨16 * (34 + j) + 12, by omega⟩ := by
  rw [buildModel, digest_cell _ ⟨33 + j, by omega⟩ _ rfl i,
    cell_block _ _ (by simp only []; omega) ⟨34 + j, by omega⟩ 12 (by decide) _ rfl]
  show blockDigest (blocksOf pub w _) i = blockCell (blocksOf pub w _) 12 _
  rw [app_digest pub w j hj, blockCell_12, blocksOf_app' pub w _ j rfl hj]
  unfold appNode
  rw [nodeIn_absorb]
  simp only [ordered, hb, Bool.false_eq_true, if_false]

/-- Append, bit 1, lanes 0..6: block 33+j's digest is the right child. -/
theorem appRight_cell (j : Nat) (hj : j < 20) (hb : appBit pub j = true) (i : Fin 8)
    (hi : i.val < 7) :
    buildModel pub w (i.castAdd 21) ⟨16 * (33 + j) + 11, by omega⟩ =
      buildModel pub w ⟨8 + i.val, by omega⟩ ⟨16 * (34 + j), by omega⟩ := by
  rw [buildModel, digest_cell _ ⟨33 + j, by omega⟩ _ rfl i,
    cell_block _ _ (by simp only []; omega) ⟨34 + j, by omega⟩ 0 (by decide) _ (by simp)]
  show blockDigest (blocksOf pub w _) i = blockCell (blocksOf pub w _) 0 _
  rw [app_digest pub w j hj, blockCell_pre, blocksOf_app' pub w _ j rfl hj]
  unfold appNode
  rw [nodeIn_pre_lt7 _ _ i hi]
  simp only [ordered, hb, if_true]

/-- Append, bit 1, lane 7 (tweak removed by the consumer offset). -/
theorem appRight7_cell [CharP K 0x7fffffff] (j : Nat) (hj : j < 20) (hb : appBit pub j = true) :
    buildModel pub w ((7 : Fin 8).castAdd 21) ⟨16 * (33 + j) + 11, by omega⟩ =
      buildModel pub w 15 ⟨16 * (34 + j), by omega⟩ + ((1051521018 : Nat) : K) := by
  rw [buildModel, digest_cell _ ⟨33 + j, by omega⟩ _ rfl 7,
    cell_block _ _ (by decide) ⟨34 + j, by omega⟩ 0 (by decide) _ (by simp)]
  show blockDigest (blocksOf pub w _) 7 = blockCell (blocksOf pub w _) 0 15 + _
  rw [app_digest pub w j hj, blockCell_pre, blocksOf_app' pub w _ j rfl hj]
  unfold appNode
  rw [nodeIn_pre_15, tweak_cancel]
  simp only [ordered, hb, if_true]

end model

#print axioms link_of
#print axioms w1_variant
#print axioms w3_bit
#print axioms w4_bit
#print axioms tweak_cancel
#print axioms blocksOf_node'
#print axioms prevBlock_digest
#print axioms pathCur_cell
#print axioms pathLeft_cell
#print axioms pathRight_cell
#print axioms pathRight7_cell
#print axioms appLeft_cell
#print axioms appRight_cell
#print axioms appRight7_cell
end R0Z.BuilderModel
