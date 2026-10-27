import R0Z.BuilderModelHash

/-! Base typing of the builder model (t2b2b/DESIGN-BUILDER-MODEL.txt §4 b, choice m5).

Every cell of `buildModel pub w` lies in the base subfield `F` when the
public input (R0P `PublicBase`) and the witness (`WitnessBase`) do.  The
Poseidon round functions preserve `F` (constants are numerals); blocks,
aux records and the layout are closed by structural lemmas over `Cells`. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K] (F : Subfield K)

/-! ### Poseidon preserves F -/

theorem foldl_add_mem (l : List K) (hl : ∀ x ∈ l, x ∈ F) (a : K) (ha : a ∈ F) :
    l.foldl (· + ·) a ∈ F := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _
        (add_mem ha (hl x List.mem_cons_self))

theorem pow5_mem (x : K) (hx : x ∈ F) : poseidonPow5 x ∈ F := by
  unfold poseidonPow5
  exact mul_mem (mul_mem (mul_mem hx hx) (mul_mem hx hx)) hx

theorem mat4_mem (v : Fin 4 → K) (hv : ∀ i, v i ∈ F) (i : Fin 4) : poseidonMat4 v i ∈ F := by
  have h0 := hv 0; have h1 := hv 1; have h2 := hv 2; have h3 := hv 3
  unfold poseidonMat4
  fin_cases i <;> simp <;>
    repeat' first | assumption | apply add_mem

theorem extLinear_mem (s : Fin 16 → K) (hs : ∀ i, s i ∈ F) (i : Fin 16) :
    poseidonExternalLinear s i ∈ F := by
  unfold poseidonExternalLinear
  have hm : ∀ (g : Fin 4) (c : Fin 4),
      poseidonMat4 (fun lane : Fin 4 => s ⟨4 * g.val + lane.val, by omega⟩) c ∈ F :=
    fun g c => mat4_mem F _ (fun _ => hs _) c
  exact add_mem (hm _ _) (add_mem (add_mem (add_mem (add_mem (zero_mem _) (hm _ _)) (hm _ _))
    (hm _ _)) (hm _ _))

theorem intLinear_mem (s : Fin 16 → K) (hs : ∀ i, s i ∈ F) (i : Fin 16) :
    poseidonInternalLinear s i ∈ F := by
  unfold poseidonInternalLinear
  have hp : (List.ofFn (fun j : Fin 15 => s j.succ)).foldl (· + ·) 0 ∈ F :=
    foldl_add_mem F _ (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hs _) 0 (zero_mem _)
  split
  · exact sub_mem hp (hs 0)
  · exact add_mem (add_mem hp (hs 0)) (mul_mem (hs i) (natCast_mem F _))

theorem extInit_mem (r : Fin 4) (l : Fin 16) : poseidonExternalInitial (K := K) r l ∈ F := by
  fin_cases r <;> fin_cases l <;> simp [poseidonExternalInitial]

theorem extFinal_mem (r : Fin 4) (l : Fin 16) : poseidonExternalFinal (K := K) r l ∈ F := by
  fin_cases r <;> fin_cases l <;> simp [poseidonExternalFinal]

theorem intConst_mem (r : Fin 14) : poseidonInternalConstants (K := K) r ∈ F := by
  fin_cases r <;> simp [poseidonInternalConstants]

theorem fullRound_mem (s c : Fin 16 → K) (hs : ∀ i, s i ∈ F) (hc : ∀ i, c i ∈ F) (i : Fin 16) :
    poseidonFullRound s c i ∈ F := by
  unfold poseidonFullRound
  exact extLinear_mem F _ (fun j => pow5_mem F _ (add_mem (hs j) (hc j))) i

theorem intRound_mem (s : Fin 16 → K) (c : K) (hs : ∀ i, s i ∈ F) (hc : c ∈ F) (i : Fin 16) :
    poseidonInternalRound s c i ∈ F := by
  unfold poseidonInternalRound
  refine intLinear_mem F _ (fun j => ?_) i
  split
  · exact pow5_mem F _ (add_mem (hs 0) hc)
  · exact hs j

theorem applyRound_mem (r : Fin 22) (s : Fin 16 → K) (hs : ∀ i, s i ∈ F) (i : Fin 16) :
    poseidonApplyRound r s i ∈ F := by
  unfold poseidonApplyRound
  split
  · exact fullRound_mem F _ _ hs (extInit_mem F _) i
  · split
    · exact intRound_mem F _ _ hs (intConst_mem F _) i
    · exact fullRound_mem F _ _ hs (extFinal_mem F _) i

theorem leadingPair_mem (s a : Fin 16 → K) (hs : ∀ i, s i ∈ F) (ha : ∀ i, a i ∈ F) (i : Fin 16) :
    poseidonLeadingPair s a i ∈ F := by
  unfold poseidonLeadingPair
  have h1 : ∀ j : Fin 16, (if j.val < 8 then s j + a j else s j) ∈ F := fun j => by
    split
    · exact add_mem (hs j) (ha j)
    · exact hs j
  exact fullRound_mem F _ _ (fullRound_mem F _ _ (extLinear_mem F _ h1) (extInit_mem F _))
    (extInit_mem F _) i

theorem transition_mem (r : Fin 11) (s a : Fin 16 → K) (hs : ∀ i, s i ∈ F) (ha : ∀ i, a i ∈ F)
    (i : Fin 16) : poseidonTransition r s a i ∈ F := by
  unfold poseidonTransition
  split
  · exact leadingPair_mem F _ _ hs ha i
  · exact applyRound_mem F _ _ (applyRound_mem F _ _ hs) i

/-! ### Blocks and layout -/

/-- Both rows a block is built from lie in F. -/
def BlockBase (b : BlockIn K) : Prop := (∀ i, b.pre i ∈ F) ∧ ∀ i, b.absorb i ∈ F

theorem blockIter_mem (b : BlockIn K) (hb : BlockBase F b) (n : Nat) (i : Fin 16) :
    blockIter b n i ∈ F := by
  induction n generalizing i with
  | zero => exact hb.1 i
  | succ n ih =>
      rw [blockIter.eq_2]
      split
      · exact transition_mem F _ _ _ ih hb.2 i
      · exact ih i

theorem blockDigest_mem (b : BlockIn K) (hb : BlockBase F b) (i : Fin 8) :
    blockDigest b i ∈ F := blockIter_mem F b hb 11 _

theorem blockOut_mem (b : BlockIn K) (hb : BlockBase F b) (i : Fin 16) :
    blockOut b i ∈ F := blockIter_mem F b hb 11 i

theorem blockCell_mem (b : BlockIn K) (hb : BlockBase F b) (l : Nat) (c : Fin 16) :
    blockCell b l c ∈ F := by
  unfold blockCell
  split
  · exact blockIter_mem F b hb l c
  · split
    · exact hb.2 c
    · exact zero_mem _

/-- Aux records in F (values are naturals, cast). -/
structure CellsBase (C : Cells K) : Prop where
  blocks : ∀ h, BlockBase F (C.blocks h)
  pathBit : ∀ l, (C.path l).bit ∈ F
  pathCur : ∀ l i, (C.path l).current i ∈ F
  pathLeft : ∀ l i, (C.path l).left i ∈ F
  pathRight : ∀ l i, (C.path l).right i ∈ F
  inOcc : C.inOcc.occupied ∈ F ∧ C.inOcc.inverse ∈ F ∧ (∀ i, C.inOcc.commitment i ∈ F) ∧
    C.inOcc.selected ∈ F
  outOcc : C.outOcc.occupied ∈ F ∧ C.outOcc.inverse ∈ F ∧ (∀ i, C.outOcc.commitment i ∈ F) ∧
    C.outOcc.selected ∈ F

theorem occCell_mem (o : OccAux K) (ho : o.occupied ∈ F ∧ o.inverse ∈ F ∧
    (∀ i, o.commitment i ∈ F) ∧ o.selected ∈ F) (c : Fin 16) : occCell o c ∈ F := by
  unfold occCell
  split
  · exact ho.1
  · split
    · exact ho.2.1
    · split
      · exact ho.2.2.1 _
      · split
        · exact ho.2.2.2
        · exact zero_mem _

theorem bitK_mem (n i : Nat) : bitK (K := K) n i ∈ F := natCast_mem F _

theorem auxCell_mem (C : Cells K) (hC : CellsBase F C) (r : Nat) (c : Fin 16) :
    auxCell C r c ∈ F := by
  have hb : ∀ v : Nat, valueBaseCell (K := K) v c ∈ F := fun v => by
    unfold valueBaseCell
    split
    · exact bitK_mem F _ _
    · split
      · exact natCast_mem F _
      · exact zero_mem _
  have hm : ∀ v : Nat, valueMidCell (K := K) v c ∈ F := fun v => by
    unfold valueMidCell
    split
    · exact bitK_mem F _ _
    · exact zero_mem _
  have hh : ∀ v : Nat, valueHiCell (K := K) v c ∈ F := fun v => by
    unfold valueHiCell
    split
    · exact bitK_mem F _ _
    · exact zero_mem _
  have hpb : ∀ l, pathBaseCell (C.path l) c ∈ F := fun l => by
    unfold pathBaseCell
    split
    · exact hC.pathBit l
    · split
      · exact hC.pathCur l _
      · exact zero_mem _
  have hps : ∀ l, pathSuccCell (C.path l) c ∈ F := fun l => by
    unfold pathSuccCell
    split
    · exact hC.pathLeft l _
    · exact hC.pathRight l _
  have hv : ∀ j, (C.values j : K) ∈ F := fun j => natCast_mem F _
  unfold auxCell
  by_cases hq : 912 ≤ r ∧ r < 1008
  · rw [dif_pos hq]
    by_cases h1 : r % 16 % 4 = 1
    · rw [if_pos h1]; exact hpb _
    · rw [if_neg h1]
      by_cases h2 : r % 16 % 4 = 2
      · rw [if_pos h2]; exact hps _
      · rw [if_neg h2]; exact zero_mem _
  rw [dif_neg hq]
  by_cases e0 : r = 1008
  · rw [if_pos e0]
    exact hb _
  rw [if_neg e0]
  by_cases e1 : r = 1009
  · rw [if_pos e1]
    exact hm _
  rw [if_neg e1]
  by_cases e2 : r = 1010
  · rw [if_pos e2]
    exact hb _
  rw [if_neg e2]
  by_cases e3 : r = 1011
  · rw [if_pos e3]
    exact hm _
  rw [if_neg e3]
  by_cases e4 : r = 1012
  · rw [if_pos e4]
    exact hb _
  rw [if_neg e4]
  by_cases e5 : r = 1013
  · rw [if_pos e5]
    exact hm _
  rw [if_neg e5]
  by_cases e6 : r = 1014
  · rw [if_pos e6]
    split
    · exact hv _
    · split
      · exact hv _
      · split
        · exact sub_mem (hv _) (hv _)
        · exact zero_mem _
  rw [if_neg e6]
  by_cases e7 : r = 1015
  · rw [if_pos e7]
    split
    · exact sub_mem (hv _) (hv _)
    · split
      · exact hv _
      · exact zero_mem _
  rw [if_neg e7]
  by_cases e8 : r = 1016
  · rw [if_pos e8]
    exact hh _
  rw [if_neg e8]
  by_cases e9 : r = 1017
  · rw [if_pos e9]
    exact occCell_mem F _ hC.inOcc c
  rw [if_neg e9]
  by_cases e10 : r = 1018
  · rw [if_pos e10]
    exact occCell_mem F _ hC.outOcc c
  rw [if_neg e10]
  by_cases e11 : r = 1020
  · rw [if_pos e11]
    exact hh _
  rw [if_neg e11]
  by_cases e12 : r = 1022
  · rw [if_pos e12]
    exact hh _
  rw [if_neg e12]
  exact zero_mem _

theorem layout_mem (C : Cells K) (hC : CellsBase F C) (c : Fin 29) (r : Fin 1024) :
    layout C c r ∈ F := by
  unfold layout
  split
  · split
    · exact blockCell_mem F _ (hC.blocks _) _ _
    · exact auxCell_mem F C hC _ _
  · exact zero_mem _

/-! ### The model's cells are in F -/

/-- The witness fields that enter the trace lie in F (Wspend over M31). -/
structure WitnessBase (w : ModelWitness K) : Prop where
  sk : ∀ i, w.sk i ∈ F
  salt : ∀ i, w.salt i ∈ F
  path : ∀ l i, (w.path l).2 i ∈ F
  pairOccupied : w.pairOccupied ∈ F
  pairSecond : ∀ i, w.pairSecond i ∈ F
  pairInverse : w.pairInverse ∈ F
  recipientOwner : ∀ i, w.recipientOwner i ∈ F
  recipientSalt : ∀ i, w.recipientSalt i ∈ F
  changeOwner : ∀ i, w.changeOwner i ∈ F
  changeSalt : ∀ i, w.changeSalt i ∈ F

theorem lo8_mem (d : Digest K) (hd : ∀ i, d i ∈ F) (l : Fin 16) : lo8 d l ∈ F := by
  unfold lo8
  split
  · exact hd _
  · exact zero_mem _

theorem spongeInit_mem (dom len : Nat) [dom.AtLeastTwo] [len.AtLeastTwo] (l : Fin 16) :
    spongeInit (K := K) (OfNat.ofNat dom) (OfNat.ofNat len) l ∈ F := by
  unfold spongeInit
  split
  · exact ofNat_mem F dom
  · split
    · exact ofNat_mem F len
    · exact zero_mem _

theorem nodeIn_base (l r : Digest K) (hl : ∀ i, l i ∈ F) (hr : ∀ i, r i ∈ F) :
    BlockBase F (nodeIn l r) := by
  refine ⟨fun i => ?_, lo8_mem F l hl⟩
  show (if i.val < 8 then 0 else if i.val = 15 then r 7 + (0x4153_1005 : K)
      else r ⟨i.val - 8, by have := i.isLt; omega⟩) ∈ F
  split
  · exact zero_mem _
  · split
    · exact add_mem (hr 7) (ofNat_mem F _)
    · exact hr _

theorem ordered_mem (a b : Digest K) (ha : ∀ i, a i ∈ F) (hb : ∀ i, b i ∈ F) (bit : Bool) :
    (∀ i, (ordered a b bit).1 i ∈ F) ∧ ∀ i, (ordered a b bit).2 i ∈ F := by
  unfold ordered
  cases bit
  · exact ⟨ha, hb⟩
  · exact ⟨hb, ha⟩

theorem noteB0_base (o : Digest K) (ho : ∀ i, o i ∈ F) : BlockBase F (noteB0 o) :=
  ⟨spongeInit_mem F 0x41530003 18, lo8_mem F o ho⟩

theorem noteB1_base (o : Digest K) (v a : K) (s : Digest K) (ho : ∀ i, o i ∈ F) (hv : v ∈ F)
    (ha : a ∈ F) (hs : ∀ i, s i ∈ F) : BlockBase F (noteB1 o v a s) := by
  refine ⟨blockIter_mem F _ (noteB0_base F o ho) 11, fun l => ?_⟩
  show noteC2 v a s l ∈ F
  unfold noteC2
  split
  · exact hv
  · split
    · exact ha
    · split
      · exact hs _
      · exact zero_mem _

theorem noteB2_base (o : Digest K) (v a : K) (s : Digest K) (ho : ∀ i, o i ∈ F) (hv : v ∈ F)
    (ha : a ∈ F) (hs : ∀ i, s i ∈ F) : BlockBase F (noteB2 o v a s) := by
  refine ⟨blockIter_mem F _ (noteB1_base F o v a s ho hv ha hs) 11, fun l => ?_⟩
  show noteC3 s l ∈ F
  unfold noteC3
  split
  · exact hs _
  · split
    · exact hs _
    · exact zero_mem _

variable {F}

theorem treeCur_mem (w : ModelWitness K) (hw : WitnessBase F w) (leaf : Digest K)
    (hl : ∀ i, leaf i ∈ F) (n : Nat) : ∀ i, treeCur w leaf n i ∈ F := by
  induction n with
  | zero => exact hl
  | succ n ih =>
      rw [treeCur.eq_2]
      split
      · exact blockDigest_mem F _ (nodeIn_base F _ _ (ordered_mem F _ _ ih (hw.path _) _).1
          (ordered_mem F _ _ ih (hw.path _) _).2)
      · exact ih

theorem emptyRootK_mem (l : Fin 20) (i : Fin 8) : emptyRootK (K := K) l i ∈ F :=
  natCast_mem F _

theorem appCur_mem (pub : Public K) (hp : PublicBase F pub) (start : Digest K)
    (hs : ∀ i, start i ∈ F) (n : Nat) : ∀ i, appCur pub start n i ∈ F := by
  have hsib : ∀ l i, appSib pub l i ∈ F := fun l i => by
    unfold appSib
    split
    · exact hp.2.2.2.2.2.2.1 l i
    · exact emptyRootK_mem l i
  induction n with
  | zero => exact hs
  | succ n ih =>
      rw [appCur.eq_2]
      split
      · exact blockDigest_mem F _ (nodeIn_base F _ _ (ordered_mem F _ _ ih (hsib _) _).1
          (ordered_mem F _ _ ih (hsib _) _).2)
      · exact ih

theorem dirK_mem (b : Bool) : dirK (K := K) b ∈ F := by
  unfold dirK
  split
  · exact one_mem _
  · exact zero_mem _

section model
variable (pub : Public K) (w : ModelWitness K) (hp : PublicBase F pub) (hw : WitnessBase F w)
include hp hw

theorem ownerDigest_mem : ∀ i, ownerDigest w i ∈ F :=
  blockDigest_mem F _ ⟨spongeInit_mem F 0x41530001 8, lo8_mem F _ hw.sk⟩

theorem inputLeaf_mem : ∀ i, inputLeaf pub w i ∈ F :=
  blockDigest_mem F _ (noteB2_base F _ _ _ _ (ownerDigest_mem pub w hp hw) (natCast_mem F _)
    hp.2.2.1 hw.salt)

theorem recipB_base (j : Nat) : BlockBase F (recipB pub w j) := by
  rw [recipB]
  cases pub.variant
  · by_cases h0 : j = 0
    · rw [if_pos h0]; exact noteB0_base F _ hw.recipientOwner
    · by_cases h1 : j = 1
      · rw [if_neg h0, if_pos h1]
        exact noteB1_base F _ _ _ _ hw.recipientOwner (natCast_mem F _) hp.2.2.1 hw.recipientSalt
      · rw [if_neg h0, if_neg h1]
        exact noteB2_base F _ _ _ _ hw.recipientOwner (natCast_mem F _) hp.2.2.1 hw.recipientSalt
  · exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem changeDigest_mem : ∀ i, changeDigest pub w i ∈ F :=
  blockDigest_mem F _ (noteB2_base F _ _ _ _ hw.changeOwner (natCast_mem F _) hp.2.2.1 hw.changeSalt)

theorem outPairB_base : BlockBase F (outPairB pub w) := by
  rw [outPairB]
  cases pub.variant
  · exact nodeIn_base F _ _ (blockDigest_mem F _ (recipB_base pub w hp hw 2))
      (changeDigest_mem pub w hp hw)
  · exact nodeIn_base F _ _ (changeDigest_mem pub w hp hw) (fun _ => zero_mem _)

theorem treeNode_base (n : Nat) (l : Fin 24) :
    BlockBase F (treeNode w (treeCur w (inputLeaf pub w) n) l) :=
  nodeIn_base F _ _ (ordered_mem F _ _ (treeCur_mem w hw _ (inputLeaf_mem pub w hp hw) n)
    (hw.path _) _).1 (ordered_mem F _ _ (treeCur_mem w hw _ (inputLeaf_mem pub w hp hw) n)
    (hw.path _) _).2

theorem appNode_base (n : Nat) (l : Fin 20) :
    BlockBase F (appNode pub (appCur pub (outPair pub w) n) l) := by
  have hsib : ∀ i, appSib pub l i ∈ F := fun i => by
    unfold appSib
    split
    · exact hp.2.2.2.2.2.2.1 l i
    · exact emptyRootK_mem l i
  have hc := appCur_mem pub hp _ (blockDigest_mem F _ (outPairB_base pub w hp hw)) n
  exact nodeIn_base F _ _ (ordered_mem F _ _ hc hsib _).1 (ordered_mem F _ _ hc hsib _).2

attribute [local irreducible] blockOut blockIter blockDigest treeCur appCur

theorem blocksOf_base (h : Fin 57) : BlockBase F (blocksOf pub w h) := by
  have h57 := h.isLt
  have hcase : h.val = 0 ∨ h.val = 1 ∨ h.val = 2 ∨ h.val = 3 ∨ (4 ≤ h.val ∧ h.val ≤ 24) ∨
      h.val = 25 ∨ h.val = 26 ∨ (27 ≤ h.val ∧ h.val ≤ 29) ∨ h.val = 30 ∨ h.val = 31 ∨
      h.val = 32 ∨ h.val = 33 ∨ (34 ≤ h.val ∧ h.val ≤ 53) ∨ 54 ≤ h.val := by omega
  have ho := ownerDigest_mem pub w hp hw
  rcases hcase with e | e | e | e | ⟨e1, e2⟩ | e | e | ⟨e1, e2⟩ | e | e | e | e | ⟨e1, e2⟩ | e
  · rw [show h = 0 from Fin.ext e]
    exact ⟨spongeInit_mem F 0x41530001 8, lo8_mem F _ hw.sk⟩
  · rw [show h = 1 from Fin.ext e]; exact noteB0_base F _ ho
  · rw [show h = 2 from Fin.ext e]
    exact noteB1_base F _ _ _ _ ho (natCast_mem F _) hp.2.2.1 hw.salt
  · rw [show h = 3 from Fin.ext e]
    exact noteB2_base F _ _ _ _ ho (natCast_mem F _) hp.2.2.1 hw.salt
  · rw [blocksOf_tree_lo pub w h e1 e2]; exact treeNode_base pub w hp hw _ _
  · rw [show h = 25 from Fin.ext e]
    exact ⟨spongeInit_mem F 0x41530002 16, lo8_mem F _ hw.sk⟩
  · rw [show h = 26 from Fin.ext e]
    show BlockBase F (nulB1 w)
    exact ⟨blockOut_mem F (nulB0 w) ⟨spongeInit_mem F 0x41530002 16, lo8_mem F _ hw.sk⟩,
      lo8_mem F _ hw.salt⟩
  · rw [blocksOf_recip pub w h e1 e2]; exact recipB_base pub w hp hw _
  · rw [show h = 30 from Fin.ext e]; exact noteB0_base F _ hw.changeOwner
  · rw [show h = 31 from Fin.ext e]
    exact noteB1_base F _ _ _ _ hw.changeOwner (natCast_mem F _) hp.2.2.1 hw.changeSalt
  · rw [show h = 32 from Fin.ext e]
    exact noteB2_base F _ _ _ _ hw.changeOwner (natCast_mem F _) hp.2.2.1 hw.changeSalt
  · rw [show h = 33 from Fin.ext e]; exact outPairB_base pub w hp hw
  · rw [blocksOf_app pub w h e1 e2]; exact appNode_base pub w hp hw _ _
  · rw [blocksOf_tree_hi pub w h e]; exact treeNode_base pub w hp hw _ _

theorem cellsOf_base : CellsBase F (cellsOf pub w) where
  blocks := blocksOf_base pub w hp hw
  pathBit := fun l => dirK_mem _
  pathCur := fun l => treeCur_mem w hw _ (inputLeaf_mem pub w hp hw) l.val
  pathLeft := fun l => (ordered_mem F _ _ (treeCur_mem w hw _ (inputLeaf_mem pub w hp hw) l.val)
    (hw.path l) _).1
  pathRight := fun l => (ordered_mem F _ _ (treeCur_mem w hw _ (inputLeaf_mem pub w hp hw) l.val)
    (hw.path l) _).2
  inOcc := ⟨hw.pairOccupied, hw.pairInverse, hw.pairSecond, dirK_mem _⟩
  outOcc := by
    show (outOccOf pub w).occupied ∈ F ∧ (outOccOf pub w).inverse ∈ F ∧
      (∀ i, (outOccOf pub w).commitment i ∈ F) ∧ (outOccOf pub w).selected ∈ F
    unfold outOccOf
    cases pub.variant
    · exact ⟨one_mem _, inv_mem (changeDigest_mem pub w hp hw 7), changeDigest_mem pub w hp hw,
        zero_mem _⟩
    · exact ⟨zero_mem _, zero_mem _, fun _ => zero_mem _, zero_mem _⟩

/-- Every cell of the model lies in the base subfield. -/
theorem buildModel_mem (c : Fin 29) (r : Fin 1024) : buildModel pub w c r ∈ F :=
  layout_mem F _ (cellsOf_base pub w hp hw) c r

end model

#print axioms transition_mem
#print axioms blockIter_mem
#print axioms auxCell_mem
#print axioms layout_mem
#print axioms blocksOf_base
#print axioms cellsOf_base
#print axioms buildModel_mem
end R0Z.BuilderModel
