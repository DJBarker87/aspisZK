import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p10
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le at' K Lane frontierLoop decodeLane)

/-! ## 8. Staging of the transcription's `decodeLane`, generic in the digest type.
Each stage is a verbatim copy of the corresponding fragment of PCVV_LaneDecodeRef.decodeLane;
`decodeLane_fact` is `rfl`, which checks the factorisation. -/
section generic
variable {Dig : Type} [DecidableEq Dig]

def hdrBad (k : K Dig) (bytes : List UInt8) : Bool :=
  bytes.length != k.accountBytes
      || sl bytes 0 4 != k.laneMagic
      || at' bytes 4 != k.laneVersion
      || (at' bytes 5).toNat >= k.laneCount
      || at' bytes 6 != UInt8.ofNat k.laneCount
      || at' bytes 7 != UInt8.ofNat k.treeDepth
      || sl bytes 8 40 != k.accountFormatBinding
      || (sl bytes 73 k.headerBytes).any (fun byte => byte != 0)

def treeBad (k : K Dig) (tree : List UInt8) : Bool :=
  sl tree 0 4 != k.treeStateMagic
      || at' tree 4 != k.treeStateVersion
      || at' tree 5 != UInt8.ofNat k.treeDepth
      || at' tree 6 != k.treeHashVersion
      || at' tree 7 != k.digestEncodingVersion

def S5 (k : K Dig) (bytes : List UInt8) (master : List UInt8) (tree : List UInt8) (nli : Nat)
    (root : Dig) : Option (Lane Dig) :=
  match frontierLoop k tree nli k.treeDepth 0 with
  | none => none
  | some frontier =>
    if nli == 0 && root != k.emptyRoots k.treeDepth then none else
    some { bump := at' bytes 72, master := master, laneId := at' bytes 5, nextLeafIndex := nli,
           root := root, frontier := frontier }

def S4 (k : K Dig) (bytes : List UInt8) (master : List UInt8) (tree : List UInt8) (nli : Nat) :
    Option (Lane Dig) :=
  match k.decodeDigest (sl tree 16 48) with
  | none => none
  | some root => S5 k bytes master tree nli root

def S3 (k : K Dig) (bytes : List UInt8) (master : List UInt8) (tree : List UInt8) :
    Option (Lane Dig) :=
  let nli := le (sl tree 8 16)
  if nli > k.pairCapacity then none else S4 k bytes master tree nli

def S2 (k : K Dig) (bytes : List UInt8) (master : List UInt8) : Option (Lane Dig) :=
  let tree := bytes.drop k.headerBytes
  if treeBad k tree = true then none else S3 k bytes master tree

def S1 (k : K Dig) (bytes : List UInt8) : Option (Lane Dig) :=
  let master := sl bytes 40 72
  if master == List.replicate 32 0 then none else S2 k bytes master

theorem decodeLane_fact (k : K Dig) (bytes : List UInt8) :
    decodeLane k bytes = if hdrBad k bytes = true then none else S1 k bytes := rfl

theorem dl_bad (k : K Dig) (bytes : List UInt8) (h : hdrBad k bytes = true) :
    decodeLane k bytes = none := by
  rw [decodeLane_fact, if_pos h]

theorem dl_ok (k : K Dig) (bytes : List UInt8) (h : hdrBad k bytes = false) :
    decodeLane k bytes = S1 k bytes := by
  have h' : ¬ (hdrBad k bytes = true) := by rw [h]; exact Bool.false_ne_true
  rw [decodeLane_fact, if_neg h']

theorem S1_bad (k : K Dig) (bytes : List UInt8) (h : (sl bytes 40 72 == List.replicate 32 0) = true) :
    S1 k bytes = none := by
  show (if (sl bytes 40 72 == List.replicate 32 0) = true then none
    else S2 k bytes (sl bytes 40 72)) = none
  rw [if_pos h]

theorem S1_ok (k : K Dig) (bytes : List UInt8) (h : (sl bytes 40 72 == List.replicate 32 0) = false) :
    S1 k bytes = S2 k bytes (sl bytes 40 72) := by
  have h' : ¬ ((sl bytes 40 72 == List.replicate 32 0) = true) := by rw [h]; exact Bool.false_ne_true
  show (if (sl bytes 40 72 == List.replicate 32 0) = true then none
    else S2 k bytes (sl bytes 40 72)) = _
  rw [if_neg h']

theorem S2_bad (k : K Dig) (bytes master : List UInt8) (h : treeBad k (bytes.drop k.headerBytes) = true) :
    S2 k bytes master = none := by
  show (if treeBad k (bytes.drop k.headerBytes) = true then none
    else S3 k bytes master (bytes.drop k.headerBytes)) = none
  rw [if_pos h]

theorem S2_ok (k : K Dig) (bytes master : List UInt8) (h : treeBad k (bytes.drop k.headerBytes) = false) :
    S2 k bytes master = S3 k bytes master (bytes.drop k.headerBytes) := by
  have h' : ¬ (treeBad k (bytes.drop k.headerBytes) = true) := by rw [h]; exact Bool.false_ne_true
  show (if treeBad k (bytes.drop k.headerBytes) = true then none
    else S3 k bytes master (bytes.drop k.headerBytes)) = _
  rw [if_neg h']

theorem S3_bad (k : K Dig) (bytes master tree : List UInt8) (h : le (sl tree 8 16) > k.pairCapacity) :
    S3 k bytes master tree = none := by
  show (if le (sl tree 8 16) > k.pairCapacity then none
    else S4 k bytes master tree (le (sl tree 8 16))) = none
  rw [if_pos h]

theorem S3_ok (k : K Dig) (bytes master tree : List UInt8) (h : ¬ le (sl tree 8 16) > k.pairCapacity) :
    S3 k bytes master tree = S4 k bytes master tree (le (sl tree 8 16)) := by
  show (if le (sl tree 8 16) > k.pairCapacity then none
    else S4 k bytes master tree (le (sl tree 8 16))) = _
  rw [if_neg h]

theorem S4_none (k : K Dig) (bytes master tree : List UInt8) (nli : Nat)
    (h : k.decodeDigest (sl tree 16 48) = none) : S4 k bytes master tree nli = none := by
  unfold S4; rw [h]

theorem S4_some (k : K Dig) (bytes master tree : List UInt8) (nli : Nat) (root : Dig)
    (h : k.decodeDigest (sl tree 16 48) = some root) :
    S4 k bytes master tree nli = S5 k bytes master tree nli root := by
  unfold S4; rw [h]

theorem S5_fnone (k : K Dig) (bytes master tree : List UInt8) (nli : Nat) (root : Dig)
    (h : frontierLoop k tree nli k.treeDepth 0 = none) :
    S5 k bytes master tree nli root = none := by
  unfold S5; rw [h]

theorem S5_bad (k : K Dig) (bytes master tree : List UInt8) (nli : Nat) (root : Dig)
    (fr : List Dig) (h : frontierLoop k tree nli k.treeDepth 0 = some fr)
    (hc : (nli == 0 && root != k.emptyRoots k.treeDepth) = true) :
    S5 k bytes master tree nli root = none := by
  unfold S5; rw [h]
  show (if (nli == 0 && root != k.emptyRoots k.treeDepth) = true then none else _) = none
  rw [if_pos hc]

theorem S5_ok (k : K Dig) (bytes master tree : List UInt8) (nli : Nat) (root : Dig)
    (fr : List Dig) (h : frontierLoop k tree nli k.treeDepth 0 = some fr)
    (hc : (nli == 0 && root != k.emptyRoots k.treeDepth) = false) :
    S5 k bytes master tree nli root =
      some { bump := at' bytes 72, master := master, laneId := at' bytes 5, nextLeafIndex := nli,
             root := root, frontier := fr } := by
  have hc' : ¬ ((nli == 0 && root != k.emptyRoots k.treeDepth) = true) := by
    rw [hc]; exact Bool.false_ne_true
  unfold S5; rw [h]
  show (if (nli == 0 && root != k.emptyRoots k.treeDepth) = true then none else _) = _
  rw [if_neg hc']

end generic

#print axioms decodeLane_fact
#print axioms S5_ok

/-! ## 9. ref-side slicing -/

theorem idx_to (b : Slice U8) (n : Usize) (h : n.val ≤ b.val.length) :
    ∃ s : Slice U8, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) b
      { «end» := n } = ok s ∧ s.val = (b.val.drop 0).take (n.val - 0) := by
  refine ⟨⟨List.slice 0 n.val b.val, ?_⟩, ?_, rfl⟩
  · have hb := b.property; simp [List.slice]; omega
  · simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice,
      core.slice.index.SliceIndexRangeToUsizeSlice.index, if_pos h]

theorem idx_range (b : Slice U8) (s e : Usize) (h1 : s.val ≤ e.val) (h2 : e.val ≤ b.val.length) :
    ∃ r : Slice U8, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) b
      { start := s, «end» := e } = ok r ∧ r.val = (b.val.drop s.val).take (e.val - s.val) := by
  refine ⟨⟨List.slice s.val e.val b.val, ?_⟩, ?_, rfl⟩
  · have hb := b.property; simp [List.slice]; omega
  · have hh : s ≤ e ∧ e.val ≤ b.val.length := ⟨by scalar_tac, h2⟩
    simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
      core.slice.index.SliceIndexRangeUsizeSlice.index, if_pos hh]

theorem idx_from (b : Slice U8) (s : Usize) (h : s.val ≤ b.val.length) :
    ∃ r : Slice U8, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) b
      { start := s } = ok r ∧ r.val = b.val.drop s.val := by
  refine ⟨b.drop s, ?_, rfl⟩
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, if_pos h]

theorem map_bt_eq_iff (l m : List U8) : l.map bt = m.map bt ↔ l = m :=
  ⟨fun h => (List.map_injective_iff.2 (fun x y hxy => bt_inj x y hxy)) h, fun h => by rw [h]⟩

theorem bne_lit (l m : List U8) (ml : List UInt8) (h : m.map bt = ml) :
    (l.map bt != ml) = !decide (l = m) := by
  subst h
  by_cases e : l = m
  · subst e; simp
  · have : ¬ (l.map bt = m.map bt) := fun h => e ((map_bt_eq_iff _ _).1 h)
    simp [e, this]

theorem at_eq (b : Slice U8) (i : Nat) (h : i < b.val.length) :
    at' (bytesOf b) i = bt (b.val[i]'h) := by
  unfold at' bytesOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  rfl

theorem lit_magic : [(65#u8 : U8), 83#u8, 76#u8, 56#u8].map bt = K0.laneMagic := by
  first | rfl | decide | (simp [bt, K0])
theorem lit_tmagic : [(65#u8 : U8), 83#u8, 80#u8, 84#u8].map bt = K0.treeStateMagic := by
  first | rfl | decide | (simp [bt, K0])
theorem lit_binding : (NCV_Reference.BINDING.val).map bt = K0.accountFormatBinding := by
  first | (with_unfolding_all rfl) | (with_unfolding_all decide) | (unfold NCV_Reference.BINDING; rfl)

end PCVY_Op50
