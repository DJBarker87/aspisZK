import R0P.Poseidon
import R0P.EmptyRoots

/-! A Lean model of the honest pair-forest builder (t2b2b/DESIGN-BUILDER-MODEL.txt §3).

The model follows the Rust stages (design §1):
* Stage B: 57 Poseidon blocks.  A block is its pre-absorption state and its
  absorption (`BlockIn`); local rows 1..11 are the canonical two-round
  transitions `poseidonTransition` (R0P), row 12 is the absorption, rows
  13..15 are zero (write_permutation / write_sponge, pair_trace.rs:268-354).
* Stage A: the forest path aux rows (pair_forest_trace.rs:142-159, rows
  912..1007), the value aux rows 1008..1016/1020/1022 and the occupancy rows
  1017/1018 (pair_trace.rs:401-468, relocated +48 by pair_forest_trace.rs:225).
* Stage M: the bank merge is the placement of blocks 34..53 (rows 544..863).
* Stage W: `cellsOf pub w` computes every block and aux record from a
  Wspend-shaped witness `ModelWitness` and the public input.
Columns 16..28 are zero (mask-only C1 and the extension columns are not read
by NonCopyHolds or CopyLinkBalance).

The witness relation is NOT fixed here; per-family theorems take named
premises (BuilderModelAux, BuilderModelHash). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

/-! ### Stage B: Poseidon blocks -/

/-- One permutation block: local row 0 and local row 12. -/
structure BlockIn (K : Type) where
  pre : Fin 16 → K
  absorb : Fin 16 → K

/-- Local rows 0..11 of a block: row 0 is the pre-state, row n+1 is the
canonical transition of row n with the absorption (R0P Poseidon.lean:315). -/
def blockIter (b : BlockIn K) : Nat → Fin 16 → K
  | 0 => b.pre
  | n + 1 => if h : n < 11 then poseidonTransition ⟨n, h⟩ (blockIter b n) b.absorb
      else blockIter b n

/-- The final state (local row 11). -/
def blockOut (b : BlockIn K) : Fin 16 → K := blockIter b 11

/-- The returned digest: the first eight lanes of the final state. -/
def blockDigest (b : BlockIn K) : Digest K := fun i => blockOut b (i.castAdd 8)

/-- The cell of a block at local row `l`, lane `c`. -/
def blockCell (b : BlockIn K) (l : Nat) (c : Fin 16) : K :=
  if l < 12 then blockIter b l c else if l = 12 then b.absorb c else 0

/-- A digest in lanes 0..7, zero in lanes 8..15. -/
def lo8 (d : Digest K) : Fin 16 → K := fun l => if h : l.val < 8 then d ⟨l.val, h⟩ else 0

/-- hash_fields_with_trace (poseidon2.rs:511-529): state[8] = domain,
state[9] = input length, everything else zero. -/
def spongeInit (dom len : K) : Fin 16 → K := fun l =>
  if l.val = 8 then dom else if l.val = 9 then len else 0

/-- write_node (pair_trace.rs:356-366): pre = [0^8, right, right[7] + tweak],
absorption = left. -/
def nodeIn (left right : Digest K) : BlockIn K :=
  ⟨fun l => if l.val < 8 then 0 else if l.val = 15 then right 7 + (0x4153_1005 : K)
      else right ⟨l.val - 8, by have := l.isLt; omega⟩, lo8 left⟩

/-- pair_trace.rs:368-375. -/
def ordered (cur sib : Digest K) (bit : Bool) : Digest K × Digest K :=
  if bit then (sib, cur) else (cur, sib)

/-- The 0/1 direction cell. -/
def dirK (b : Bool) : K := if b then 1 else 0

/-! ### Stage A: auxiliary records and their cells -/

structure PathAux (K : Type) where
  bit : K
  current : Digest K
  left : Digest K
  right : Digest K

structure OccAux (K : Type) where
  occupied : K
  inverse : K
  commitment : Digest K
  selected : K

/-- The builder's cell content before placement. -/
structure Cells (K : Type) where
  blocks : Fin 57 → BlockIn K
  path : Fin 24 → PathAux K
  values : Fin 3 → Nat
  inOcc : OccAux K
  outOcc : OccAux K

/-- Bit `i` of `n` as a field cell.  `bitK_eq_shift` is the Rust form
`M31((raw >> bit) & 1)` (pair_trace.rs:404-412). -/
def bitK (n i : Nat) : K := ((n / 2 ^ i % 2 : Nat) : K)

/-- Value base row (1008 + 2j): bits 0..9 of v, raw v in column 10. -/
def valueBaseCell (v : Nat) (c : Fin 16) : K :=
  if c.val < 10 then bitK v c.val else if c.val = 10 then (v : K) else 0

/-- Value successor row (1009 + 2j): bits 10..19. -/
def valueMidCell (v : Nat) (c : Fin 16) : K :=
  if c.val < 10 then bitK (v / 1024) c.val else 0

/-- Value xor-12 row (1020, 1022, 1016): bits 20..29. -/
def valueHiCell (v : Nat) (c : Fin 16) : K :=
  if c.val < 10 then bitK (v / 1048576) c.val else 0

/-- write_occupancy (pair_trace.rs:439-468). -/
def occCell (o : OccAux K) (c : Fin 16) : K :=
  if c.val = 0 then o.occupied else if c.val = 1 then o.inverse
  else if h : c.val < 10 then o.commitment ⟨c.val - 2, by omega⟩
  else if c.val = 10 then o.selected else 0

/-- write_forest_path_aux base row (pair_forest_trace.rs:152-154). -/
def pathBaseCell (p : PathAux K) (c : Fin 16) : K :=
  if c.val = 0 then p.bit else if h : c.val < 9 then p.current ⟨c.val - 1, by omega⟩ else 0

/-- write_forest_path_aux successor row (pair_forest_trace.rs:155-156). -/
def pathSuccCell (p : PathAux K) (c : Fin 16) : K :=
  if h : c.val < 8 then p.left ⟨c.val, h⟩ else p.right ⟨c.val - 8, by have := c.isLt; omega⟩

/-- Rows 912..1023 (blocks 57..63). -/
def auxCell (C : Cells K) (r : Nat) (c : Fin 16) : K :=
  if h : 912 ≤ r ∧ r < 1008 then
    if r % 16 % 4 = 1 then
      pathBaseCell (C.path ⟨4 * ((r - 912) / 16) + r % 16 / 4, by omega⟩) c
    else if r % 16 % 4 = 2 then
      pathSuccCell (C.path ⟨4 * ((r - 912) / 16) + r % 16 / 4, by omega⟩) c
    else 0
  else if r = 1008 then valueBaseCell (C.values 0) c
  else if r = 1009 then valueMidCell (C.values 0) c
  else if r = 1010 then valueBaseCell (C.values 1) c
  else if r = 1011 then valueMidCell (C.values 1) c
  else if r = 1012 then valueBaseCell (C.values 2) c
  else if r = 1013 then valueMidCell (C.values 2) c
  else if r = 1014 then
    (if c.val = 0 then (C.values 0 : K) else if c.val = 1 then (C.values 1 : K)
      else if c.val = 2 then (C.values 0 : K) - (C.values 1 : K) else 0)
  else if r = 1015 then
    (if c.val = 0 then (C.values 0 : K) - (C.values 1 : K)
      else if c.val = 1 then (C.values 2 : K) else 0)
  else if r = 1016 then valueHiCell (C.values 2) c
  else if r = 1017 then occCell C.inOcc c
  else if r = 1018 then occCell C.outOcc c
  else if r = 1020 then valueHiCell (C.values 0) c
  else if r = 1022 then valueHiCell (C.values 1) c
  else 0

/-! ### Placement (stages B, A, M) -/

/-- The 29-column trace: blocks 0..56 in rows 0..911, aux rows above,
columns 16..28 zero. -/
def layout (C : Cells K) : Trace K := fun c r =>
  if hc : c.val < 16 then
    if hb : r.val / 16 < 57 then blockCell (C.blocks ⟨r.val / 16, hb⟩) (r.val % 16) ⟨c.val, hc⟩
    else auxCell C r.val ⟨c.val, hc⟩
  else 0

theorem layout_aux (C : Cells K) (c : Fin 29) (r : Fin 1024) (hc : c.val < 16)
    (hr : 57 ≤ r.val / 16) : layout C c r = auxCell C r.val ⟨c.val, hc⟩ := by
  unfold layout
  rw [dif_pos hc, dif_neg (by omega)]

theorem layout_block (C : Cells K) (c : Fin 29) (r : Fin 1024) (hc : c.val < 16)
    (h : Fin 57) (hr : r.val / 16 = h.val) :
    layout C c r = blockCell (C.blocks h) (r.val % 16) ⟨c.val, hc⟩ := by
  have h57 := h.isLt
  unfold layout
  rw [dif_pos hc, dif_pos (by omega)]
  have he : (⟨r.val / 16, by omega⟩ : Fin 57) = h := Fin.ext hr
  rw [he]

theorem layout_high (C : Cells K) (c : Fin 29) (r : Fin 1024) (hc : 16 ≤ c.val) :
    layout C c r = 0 := by
  unfold layout
  rw [dif_neg (by omega)]

/-- Openings of a row whose row, successor and xor-12 rows are all aux rows. -/
theorem rowOpenings_aux (C : Cells K) (b : Fin 1024) (hb : 57 ≤ b.val / 16)
    (hs : 57 ≤ (succRow b).val / 16) (hx : 57 ≤ (xor12Row b).val / 16) :
    rowOpenings (layout C) b =
      ⟨auxCell C b.val, auxCell C (succRow b).val, auxCell C (xor12Row b).val⟩ := by
  unfold rowOpenings
  congr 1 <;> funext c <;> exact layout_aux C _ _ c.isLt (by assumption)

/-! ### Bits -/

theorem nat_bits (k n : Nat) : n % 2 ^ k = ∑ i ∈ Finset.range k, n / 2 ^ i % 2 * 2 ^ i := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Nat.mod_pow_succ, ih, Finset.sum_range_succ]; ring

theorem bitK_01 (n i : Nat) : bitK (K := K) n i = 0 ∨ bitK (K := K) n i = 1 := by
  unfold bitK
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> rw [h] <;> simp

/-- Rust form of the bit cells (pair_trace.rs:404-412, `(raw >> bit) & 1`). -/
theorem bitK_eq_shift (n i : Nat) : bitK (K := K) n i = ((n >>> i &&& 1 : Nat) : K) := by
  unfold bitK
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem bitK_mid (n i : Nat) : bitK (K := K) (n / 1024) i = bitK (K := K) n (10 + i) := by
  unfold bitK
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

theorem bitK_hi (n i : Nat) : bitK (K := K) (n / 1048576) i = bitK (K := K) n (20 + i) := by
  unfold bitK
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- Ten-bit reconstruction in the literal order of R0P `valueReconstruct10`. -/
theorem chunk10 (n : Nat) : ((n % 1024 : Nat) : K) =
    bitK n 0 + 2 * bitK n 1 + 4 * bitK n 2 + 8 * bitK n 3 + 16 * bitK n 4 +
      32 * bitK n 5 + 64 * bitK n 6 + 128 * bitK n 7 + 256 * bitK n 8 + 512 * bitK n 9 := by
  have h : n % 1024 = ∑ i ∈ Finset.range 10, n / 2 ^ i % 2 * 2 ^ i := nat_bits 10 n
  rw [h]
  push_cast
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bitK]
  ring

/-! ### Stage W: the witness and the computed cells -/

/-- Wspend-shaped witness (SpendRelation.lean:15 on the spend path), with the
pair leaf unfolded into its four fields. -/
structure ModelWitness (K : Type) where
  inputValue : Fin (2 ^ 30)
  outputValue : Fin (2 ^ 30)
  changeValue : Fin (2 ^ 30)
  sk : Digest K
  salt : Digest K
  path : Fin 24 → Bool × Digest K
  pairFirst : Digest K
  pairOccupied : K
  pairSecond : Digest K
  pairInverse : K
  recipientOwner : Digest K
  recipientSalt : Digest K
  changeOwner : Digest K
  changeSalt : Digest K

/-- Note chunk 1 (note_input[8..16)): value, asset, salt[0..6). -/
def noteC2 (value asset : K) (salt : Digest K) : Fin 16 → K := fun l =>
  if l.val = 0 then value else if l.val = 1 then asset
  else if h : l.val < 8 then salt ⟨l.val - 2, by omega⟩ else 0

/-- Note chunk 2 (note_input[16..18)): salt[6], salt[7]. -/
def noteC3 (salt : Digest K) : Fin 16 → K := fun l =>
  if l.val = 0 then salt 6 else if l.val = 1 then salt 7 else 0

def noteB0 (owner : Digest K) : BlockIn K := ⟨spongeInit 0x4153_0003 18, lo8 owner⟩
def noteB1 (owner : Digest K) (value asset : K) (salt : Digest K) : BlockIn K :=
  ⟨blockOut (noteB0 owner), noteC2 value asset salt⟩
def noteB2 (owner : Digest K) (value asset : K) (salt : Digest K) : BlockIn K :=
  ⟨blockOut (noteB1 owner value asset salt), noteC3 salt⟩
def noteDigest (owner : Digest K) (value asset : K) (salt : Digest K) : Digest K :=
  blockDigest (noteB2 owner value asset salt)

variable (pub : Public K) (w : ModelWitness K)

def ownerB : BlockIn K := ⟨spongeInit 0x4153_0001 8, lo8 w.sk⟩
def ownerDigest : Digest K := blockDigest (ownerB w)
def nulB0 : BlockIn K := ⟨spongeInit 0x4153_0002 16, lo8 w.sk⟩
def nulB1 : BlockIn K := ⟨blockOut (nulB0 w), lo8 w.salt⟩
def nullifierDigest : Digest K := blockDigest (nulB1 w)

def inputLeaf : Digest K :=
  noteDigest (ownerDigest w) (w.inputValue.val : K) pub.assetId w.salt

/-- Membership node at level l (blocks 4..24 and 54..56). -/
def treeNode (cur : Digest K) (l : Fin 24) : BlockIn K :=
  nodeIn (ordered cur (w.path l).2 (w.path l).1).1 (ordered cur (w.path l).2 (w.path l).1).2

/-- The running membership digest: level 0 is the input leaf. -/
def treeCur (leaf : Digest K) : Nat → Digest K
  | 0 => leaf
  | n + 1 => if h : n < 24 then blockDigest (treeNode w (treeCur leaf n) ⟨n, h⟩)
      else treeCur leaf n

/-- build_late_append (pair_trace.rs:579-586): the append bit. -/
def appBit (l : Nat) : Bool := decide (((pub.nextPairIndex >>> l) &&& 1) ≠ 0)

def emptyRootK (l : Fin 20) : Digest K := fun i => ((emptyRootsNat l.castSucc i : Nat) : K)

def appSib (l : Fin 20) : Digest K :=
  if appBit pub l.val then pub.snapshotFrontier l else emptyRootK l

def appNode (cur : Digest K) (l : Fin 20) : BlockIn K :=
  nodeIn (ordered cur (appSib pub l) (appBit pub l.val)).1
    (ordered cur (appSib pub l) (appBit pub l.val)).2

def appCur (start : Digest K) : Nat → Digest K
  | 0 => start
  | n + 1 => if h : n < 20 then blockDigest (appNode pub (appCur start n) ⟨n, h⟩)
      else appCur start n

/-- Blocks 27..29: the recipient note, or three zero permutations
(pair_trace.rs:741-743) for a withdrawal. -/
def recipB (j : Nat) : BlockIn K :=
  match pub.variant with
  | .privateTransfer =>
      if j = 0 then noteB0 w.recipientOwner
      else if j = 1 then noteB1 w.recipientOwner (w.outputValue.val : K) pub.assetId w.recipientSalt
      else noteB2 w.recipientOwner (w.outputValue.val : K) pub.assetId w.recipientSalt
  | .withdrawal => ⟨0, 0⟩

def recipientDigest : Digest K := blockDigest (recipB pub w 2)

def changeDigest : Digest K :=
  noteDigest w.changeOwner (w.changeValue.val : K) pub.assetId w.changeSalt

def outPairB : BlockIn K :=
  match pub.variant with
  | .privateTransfer => nodeIn (recipientDigest pub w) (changeDigest pub w)
  | .withdrawal => nodeIn (changeDigest pub w) 0

def outPair : Digest K := blockDigest (outPairB pub w)

/-- The 57 blocks in the forest layout (pair_tree_profile.rs:326-349 roles,
blocks 54..56 from pair_forest_trace.rs:229-240). -/
def blocksOf (h : Fin 57) : BlockIn K :=
  if h.val = 0 then ownerB w
  else if h.val = 1 then noteB0 (ownerDigest w)
  else if h.val = 2 then noteB1 (ownerDigest w) (w.inputValue.val : K) pub.assetId w.salt
  else if h.val = 3 then noteB2 (ownerDigest w) (w.inputValue.val : K) pub.assetId w.salt
  else if h4 : h.val ≤ 24 then
    treeNode w (treeCur w (inputLeaf pub w) (h.val - 4)) ⟨h.val - 4, by omega⟩
  else if h.val = 25 then nulB0 w
  else if h.val = 26 then nulB1 w
  else if h.val ≤ 29 then recipB pub w (h.val - 27)
  else if h.val = 30 then noteB0 w.changeOwner
  else if h.val = 31 then noteB1 w.changeOwner (w.changeValue.val : K) pub.assetId w.changeSalt
  else if h.val = 32 then noteB2 w.changeOwner (w.changeValue.val : K) pub.assetId w.changeSalt
  else if h.val = 33 then outPairB pub w
  else if h53 : h.val ≤ 53 then
    appNode pub (appCur pub (outPair pub w) (h.val - 34)) ⟨h.val - 34, by omega⟩
  else treeNode w (treeCur w (inputLeaf pub w) (h.val - 33))
    ⟨h.val - 33, by have := h.isLt; omega⟩

/-- Path aux record at level l: the same current/sibling/bit as the node. -/
def pathAuxOf (l : Fin 24) : PathAux K :=
  ⟨dirK (w.path l).1, treeCur w (inputLeaf pub w) l.val,
    (ordered (treeCur w (inputLeaf pub w) l.val) (w.path l).2 (w.path l).1).1,
    (ordered (treeCur w (inputLeaf pub w) l.val) (w.path l).2 (w.path l).1).2⟩

def valuesOf : Fin 3 → Nat := ![w.inputValue.val, w.outputValue.val, w.changeValue.val]

def inOccOf : OccAux K := ⟨w.pairOccupied, w.pairInverse, w.pairSecond, dirK (w.path 0).1⟩

/-- two_outputs / single_output (pair_tree_profile.rs:193-226). -/
def outOccOf : OccAux K :=
  match pub.variant with
  | .privateTransfer => ⟨1, (changeDigest pub w 7)⁻¹, changeDigest pub w, 0⟩
  | .withdrawal => ⟨0, 0, 0, 0⟩

def cellsOf : Cells K :=
  ⟨blocksOf pub w, pathAuxOf pub w, valuesOf w, inOccOf w, outOccOf pub w⟩

/-- The model builder. -/
def buildModel : Trace K := layout (cellsOf pub w)

#print axioms blockIter
#print axioms layout
#print axioms layout_aux
#print axioms layout_block
#print axioms layout_high
#print axioms rowOpenings_aux
#print axioms nat_bits
#print axioms bitK_01
#print axioms bitK_eq_shift
#print axioms bitK_mid
#print axioms bitK_hi
#print axioms chunk10
#print axioms cellsOf
#print axioms buildModel
end R0Z.BuilderModel
