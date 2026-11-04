import R0Z.BuilderModelCopyKinds

/-! The 24 one-off copy links of the builder model (sponge chaining, digest
reuse, shared absorptions, value/positivity cells, occupancy cells), each as a
named cell lemma.  The only witness premise is `pairRight` (the input pair
leaf's second commitment is the right child of block 4, i.e. the path-0
sibling and bit are the pair's other commitment and selected side). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

theorem blockCell_out (b : BlockIn K) (c : Fin 16) : blockCell b 11 c = blockOut b c := rfl

theorem lo8_lt (d : Digest K) (i : Fin 8) : lo8 d ⟨i.val, by omega⟩ = d i := by
  unfold lo8; rw [dif_pos i.isLt]

section model
variable (pub : Public K) (w : ModelWitness K)

/-! ### Block-role facts (small structural equalities) -/

theorem pre_2 : (blocksOf pub w 2).pre = blockOut (blocksOf pub w 1) := rfl
theorem pre_3 : (blocksOf pub w 3).pre = blockOut (blocksOf pub w 2) := rfl
theorem pre_26 : (blocksOf pub w 26).pre = blockOut (blocksOf pub w 25) := rfl
theorem pre_31 : (blocksOf pub w 31).pre = blockOut (blocksOf pub w 30) := rfl
theorem pre_32 : (blocksOf pub w 32).pre = blockOut (blocksOf pub w 31) := rfl

theorem pre_28 (hv : pub.variant = .privateTransfer) :
    (blocksOf pub w 28).pre = blockOut (blocksOf pub w 27) := by
  show (recipB pub w 1).pre = blockOut (recipB pub w 0)
  unfold recipB; rw [hv]; rfl

theorem pre_29 (hv : pub.variant = .privateTransfer) :
    (blocksOf pub w 29).pre = blockOut (blocksOf pub w 28) := by
  show (recipB pub w 2).pre = blockOut (recipB pub w 1)
  unfold recipB; rw [hv]; rfl

theorem ab_1 (i : Fin 8) :
    (blocksOf pub w 1).absorb ⟨i.val, by omega⟩ = blockDigest (blocksOf pub w 0) i :=
  lo8_lt _ i

theorem ab_33pt (hv : pub.variant = .privateTransfer) (i : Fin 8) :
    (blocksOf pub w 33).absorb ⟨i.val, by omega⟩ = blockDigest (blocksOf pub w 29) i := by
  show (outPairB pub w).absorb _ = blockDigest (recipB pub w 2) i
  unfold outPairB; rw [hv]
  exact lo8_lt _ i

theorem ab_33wd (hv : pub.variant = .withdrawal) (i : Fin 8) :
    (blocksOf pub w 33).absorb ⟨i.val, by omega⟩ = blockDigest (blocksOf pub w 32) i := by
  show (outPairB pub w).absorb _ = _
  unfold outPairB; rw [hv]
  exact lo8_lt _ i

theorem e480 (i : Fin 8) :
    (blocksOf pub w 0).absorb ⟨i.val, by omega⟩ = (blocksOf pub w 25).absorb ⟨i.val, by omega⟩ := rfl

theorem e481 (j : Fin 6) :
    (blocksOf pub w 2).absorb ⟨2 + j.val, by omega⟩ = (blocksOf pub w 26).absorb ⟨j.val, by omega⟩ := by
  show noteC2 _ _ w.salt ⟨2 + j.val, _⟩ = lo8 w.salt ⟨j.val, _⟩
  unfold noteC2 lo8
  rw [if_neg (by simp), if_neg (by simp; omega), dif_pos (by simp; omega), dif_pos (by simp; omega)]
  exact congrArg w.salt (Fin.ext (by simp))

theorem e482 (j : Fin 2) :
    (blocksOf pub w 3).absorb ⟨j.val, by omega⟩ = (blocksOf pub w 26).absorb ⟨6 + j.val, by omega⟩ := by
  show noteC3 w.salt ⟨j.val, _⟩ = lo8 w.salt ⟨6 + j.val, _⟩
  unfold noteC3 lo8
  rw [dif_pos (by simp; omega)]
  fin_cases j
  · rfl
  · rfl

attribute [local irreducible] blockOut blockIter blockDigest treeCur appCur

/-! ### Cell kinds -/

theorem chain_cell (h h' : Fin 57) (hpre : (blocksOf pub w h').pre = blockOut (blocksOf pub w h))
    (c : Fin 16) :
    buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + 11, by have := h.isLt; omega⟩ =
      buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h'.val + 0, by have := h'.isLt; omega⟩ := by
  rw [buildModel, cell_block _ _ c.isLt h 11 (by decide) _ rfl,
    cell_block _ _ c.isLt h' 0 (by decide) _ rfl]
  show blockCell (blocksOf pub w h) 11 c = blockCell (blocksOf pub w h') 0 c
  rw [blockCell_out, blockCell_pre, hpre]

theorem da_cell (h h' : Fin 57)
    (hab : ∀ i : Fin 8, (blocksOf pub w h').absorb ⟨i.val, by omega⟩ = blockDigest (blocksOf pub w h) i)
    (i : Fin 8) :
    buildModel pub w (i.castAdd 21) ⟨16 * h.val + 11, by have := h.isLt; omega⟩ =
      buildModel pub w ⟨i.val, by omega⟩ ⟨16 * h'.val + 12, by have := h'.isLt; omega⟩ := by
  rw [buildModel, digest_cell _ h _ rfl i,
    cell_block _ _ (by simp only []; omega) h' 12 (by decide) _ rfl]
  show blockDigest (blocksOf pub w h) i = blockCell (blocksOf pub w h') 12 _
  rw [blockCell_12, hab]

theorem aa_cell (h h' : Fin 57) (c c' : Fin 16)
    (e : (blocksOf pub w h).absorb c = (blocksOf pub w h').absorb c') :
    buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + 12, by have := h.isLt; omega⟩ =
      buildModel pub w ⟨c'.val, by omega⟩ ⟨16 * h'.val + 12, by have := h'.isLt; omega⟩ := by
  rw [buildModel, cell_block _ _ c.isLt h 12 (by decide) _ rfl,
    cell_block _ _ c'.isLt h' 12 (by decide) _ rfl]
  show blockCell (blocksOf pub w h) 12 c = blockCell (blocksOf pub w h') 12 c'
  rw [blockCell_12, blockCell_12, e]

/-! ### Value and positivity cells -/

theorem v483 : buildModel pub w 0 44 = buildModel pub w 10 1008 := by
  rw [buildModel, cell_block _ _ (by decide) 2 12 (by decide) _ rfl,
    cell_aux _ _ (by decide) _ (by decide)]
  show (blocksOf pub w 2).absorb 0 = auxCell _ 1008 10
  rw [aux_1008]
  rfl

theorem v484 (hv : pub.variant = .privateTransfer) :
    buildModel pub w 0 460 = buildModel pub w 10 1010 := by
  rw [buildModel, cell_block _ _ (by decide) 28 12 (by decide) _ rfl,
    cell_aux _ _ (by decide) _ (by decide)]
  show (recipB pub w 1).absorb 0 = auxCell _ 1010 10
  rw [aux_1010]
  unfold recipB; rw [hv]
  rfl

theorem v485 : buildModel pub w 0 508 = buildModel pub w 10 1012 := by
  rw [buildModel, cell_block _ _ (by decide) 31 12 (by decide) _ rfl,
    cell_aux _ _ (by decide) _ (by decide)]
  show (blocksOf pub w 31).absorb 0 = auxCell _ 1012 10
  rw [aux_1012]
  rfl

theorem aux_1014 (C : Cells K) (c : Fin 16) : auxCell C 1014 c =
    (if c.val = 0 then (C.values 0 : K) else if c.val = 1 then (C.values 1 : K)
      else if c.val = 2 then (C.values 0 : K) - (C.values 1 : K) else 0) := by
  simp [auxCell]

theorem aux_1015 (C : Cells K) (c : Fin 16) : auxCell C 1015 c =
    (if c.val = 0 then (C.values 0 : K) - (C.values 1 : K)
      else if c.val = 1 then (C.values 2 : K) else 0) := by
  simp [auxCell]

theorem p486 : buildModel pub w 10 1008 = buildModel pub w 0 1014 := by
  rw [buildModel, cell_aux _ _ (by decide) _ (by decide), cell_aux _ _ (by decide) _ (by decide)]
  show auxCell _ 1008 10 = auxCell _ 1014 0
  rw [aux_1008, aux_1014]
  rfl

theorem p487 : buildModel pub w 10 1010 = buildModel pub w 1 1014 := by
  rw [buildModel, cell_aux _ _ (by decide) _ (by decide), cell_aux _ _ (by decide) _ (by decide)]
  show auxCell _ 1010 10 = auxCell _ 1014 1
  rw [aux_1010, aux_1014]
  rfl

theorem p488 : buildModel pub w 10 1012 = buildModel pub w 1 1015 := by
  rw [buildModel, cell_aux _ _ (by decide) _ (by decide), cell_aux _ _ (by decide) _ (by decide)]
  show auxCell _ 1012 10 = auxCell _ 1015 1
  rw [aux_1012, aux_1015]
  rfl

theorem p489 : buildModel pub w 2 1014 = buildModel pub w 0 1015 := by
  rw [buildModel, cell_aux _ _ (by decide) _ (by decide), cell_aux _ _ (by decide) _ (by decide)]
  show auxCell _ 1014 2 = auxCell _ 1015 0
  rw [aux_1014, aux_1015]
  rfl

/-! ### Occupancy cells -/

/-- Witness premise for link 1124073490: the input pair's second commitment
is the right child of the pair node (block 4). -/
def PairRight : Prop := w.pairSecond = (ordered (inputLeaf pub w) (w.path 0).2 (w.path 0).1).2

theorem block4 : blocksOf pub w 4 =
    nodeIn (ordered (inputLeaf pub w) (w.path 0).2 (w.path 0).1).1
      (ordered (inputLeaf pub w) (w.path 0).2 (w.path 0).1).2 := by
  show treeNode w (treeCur w (inputLeaf pub w) 0) 0 = _
  rw [treeCur.eq_1]
  rfl

theorem o490 (hR : PairRight pub w) (j : Fin 8) (hj : j.val < 7) :
    buildModel pub w ⟨8 + j.val, by omega⟩ 64 = buildModel pub w ⟨2 + j.val, by omega⟩ 1017 := by
  rw [buildModel, cell_block _ _ (by simp only []; omega) 4 0 (by decide) _ rfl,
    cell_aux _ _ (by simp only []; omega) _ (by decide)]
  show blockCell (blocksOf pub w 4) 0 _ = auxCell _ 1017 _
  rw [blockCell_pre, block4, aux_1017, nodeIn_pre_lt7 _ _ j hj, occCell_lane _ j]
  show _ = w.pairSecond j
  rw [hR]

theorem o490_7 [CharP K 0x7fffffff] (hR : PairRight pub w) :
    buildModel pub w 15 64 + ((1051521018 : Nat) : K) = buildModel pub w 9 1017 := by
  rw [buildModel, cell_block _ _ (by decide) 4 0 (by decide) _ rfl,
    cell_aux _ _ (by decide) _ (by decide)]
  show blockCell (blocksOf pub w 4) 0 15 + _ = auxCell _ 1017 9
  rw [blockCell_pre, block4, aux_1017, nodeIn_pre_15, tweak_cancel,
    show occCell (cellsOf pub w).inOcc 9 = (cellsOf pub w).inOcc.commitment 7 from
      occCell_lane _ 7 (by decide)]
  show _ = w.pairSecond 7
  rw [hR]

theorem o491 : buildModel pub w 0 913 = buildModel pub w 10 1017 := by
  rw [buildModel, cell_aux _ _ (by decide) _ (by decide), cell_aux _ _ (by decide) _ (by decide)]
  show auxCell _ (pathBase 0) 0 = auxCell _ 1017 10
  rw [pathBase_aux, aux_1017]
  rfl

theorem o492 (hv : pub.variant = .privateTransfer) (j : Fin 8) :
    buildModel pub w (j.castAdd 21) 523 = buildModel pub w ⟨2 + j.val, by omega⟩ 1018 := by
  rw [buildModel, digest_cell _ 32 523 rfl j, cell_aux _ _ (by simp only []; omega) _ (by decide)]
  show blockDigest (blocksOf pub w 32) j = auxCell _ 1018 _
  rw [aux_1018, occCell_lane _ j]
  show _ = (outOccOf pub w).commitment j
  unfold outOccOf; rw [hv]
  rfl

theorem o495 (j : Fin 8) (hj : j.val < 7) :
    buildModel pub w ⟨2 + j.val, by omega⟩ 1018 = buildModel pub w ⟨8 + j.val, by omega⟩ 528 := by
  rw [buildModel, cell_aux _ _ (by simp only []; omega) _ (by decide),
    cell_block _ _ (by simp only []; omega) 33 0 (by decide) _ rfl]
  show auxCell _ 1018 _ = blockCell (outPairB pub w) 0 _
  rw [aux_1018, occCell_lane _ j, blockCell_pre]
  show (outOccOf pub w).commitment j = _
  unfold outOccOf outPairB
  cases pub.variant
  · exact (nodeIn_pre_lt7 _ _ j hj).symm
  · exact (nodeIn_pre_lt7 _ _ j hj).symm

theorem o495_7 [CharP K 0x7fffffff] :
    buildModel pub w 9 1018 = buildModel pub w 15 528 + ((1051521018 : Nat) : K) := by
  rw [buildModel, cell_aux _ _ (by decide) _ (by decide),
    cell_block _ _ (by decide) 33 0 (by decide) _ rfl]
  show auxCell _ 1018 9 = blockCell (outPairB pub w) 0 15 + _
  rw [aux_1018, show occCell (cellsOf pub w).outOcc 9 = (cellsOf pub w).outOcc.commitment 7 from
      occCell_lane _ 7 (by decide), blockCell_pre]
  show (outOccOf pub w).commitment 7 = _
  unfold outOccOf outPairB
  cases pub.variant
  · rw [nodeIn_pre_15, tweak_cancel]
  · rw [nodeIn_pre_15, tweak_cancel]

end model

#print axioms chain_cell
#print axioms da_cell
#print axioms aa_cell
#print axioms e481
#print axioms e482
#print axioms v484
#print axioms p489
#print axioms o490
#print axioms o490_7
#print axioms o491
#print axioms o492
#print axioms o495
#print axioms o495_7
end R0Z.BuilderModel
