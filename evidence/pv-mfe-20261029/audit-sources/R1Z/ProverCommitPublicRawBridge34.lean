import R1Z.ProverCommitPublicWhole34
import R1Z.ProverCommitPublicRaw34

/-! Fixed fieldwise projection from the actual extracted source carriers to
PublicRawCore, with successful byte agreement. This is a Lean 4.31 theorem;
checking the shared core separately under 4.32 does not merge the kernels or
supply a Rust runtime/extraction theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1

namespace AspisR1PublicSerializer.RawBridge431
open FieldsRefinement431
open Whole431

def rawByte (x : Std.U8) : PublicRawCore.Byte := x.bv.toFin

def rawWord (x : Field) : PublicRawCore.Word := x.bv.toFin

def rawIndex (x : Std.U64) : PublicRawCore.Index := x.bv.toFin

def projectDigest (d : Array Field 8#usize) : PublicRawCore.Digest := fun i =>
  rawWord (d.val[i.val]'(by simpa [d.property] using i.isLt))

def projectFrontier (f : Frontier431.Frontier) : PublicRawCore.Frontier := fun l =>
  projectDigest (f.val[l.val]'(by simpa [f.property] using l.isLt))

/-- The source fields copied here are fixed, including live rather than
candidate next_pair_index. Omitted source metadata is not silently bound. -/
def projectCommon (anchor nullifier : Array Field 8#usize) (asset : Field)
    (change : Array Field 8#usize) (t : Transition) : PublicRawCore.Common :=
  { anchor := projectDigest anchor
    nullifier := projectDigest nullifier
    assetId := rawWord asset
    change := projectDigest change
    nextPairIndex := rawIndex t.live_snapshot.next_pair_index
    snapshotFrontier := projectFrontier t.live_snapshot.frontier
    nextRoot := projectDigest t.candidate_afterstate.next_root
    nextFrontier := projectFrontier t.candidate_afterstate.next_frontier }

def project : Public → PublicRawCore.Public
  | .Transfer p t => .transfer
    (projectCommon p.anchor_root p.nullifier p.asset_id p.change_commitment t)
    (projectDigest p.recipient_commitment)
  | .Withdrawal p t => .withdrawal
    (projectCommon p.anchor_root p.nullifier p.asset_id p.change_commitment t)
    (rawWord p.amount)

theorem rawWord_val (x : Field) : (rawWord x).val = x.val := rfl

theorem rawByte_val (x : Std.U8) : (rawByte x).val = x.val := rfl

theorem rawIndex_val (x : Std.U64) : (rawIndex x).val = x.val := rfl

theorem wordBytes_agree (x : Field) :
    (wordBytes x).map rawByte = PublicRawCore.wordBytes (rawWord x) := by
  apply List.ext_getElem
  · simp only [List.length_map, wordBytes_length, PublicRawCore.wordBytes,
      List.length_ofFn]
  · intro i hi hj
    have hi4 : i < 4 := by simpa only [List.length_map, wordBytes_length] using hi
    have cases4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases4 with rfl | rfl | rfl | rfl <;>
      apply Fin.ext <;>
      simp [wordBytes, PublicRawCore.wordBytes, PublicRawCore.wordByte,
        PublicRawCore.byteMod, rawByte, rawWord, core.num.U32.to_le_bytes,
        BitVec.toLEBytes, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow] <;> omega

theorem indexBytes_agree (x : Std.U64) :
    (core.num.U64.to_le_bytes x).val.map rawByte = PublicRawCore.indexBytes (rawIndex x) := by
  apply List.ext_getElem
  · simp [core.num.U64.to_le_bytes, PublicRawCore.indexBytes]
  · intro i hi hj
    have hi8 : i < 8 := by
      simpa [core.num.U64.to_le_bytes] using hi
    have cases8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      omega
    rcases cases8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply Fin.ext <;>
      simp [PublicRawCore.indexBytes, PublicRawCore.indexByte,
        PublicRawCore.lowWord, PublicRawCore.highWord, PublicRawCore.wordByte,
        PublicRawCore.byteMod, rawByte, rawIndex, core.num.U64.to_le_bytes,
        BitVec.toLEBytes, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow] <;> omega

/-- Symbolic enumeration: no concrete digest or frontier entries are reduced. -/
theorem ofFn_map_getElem {α β : Type} (xs : List α) (n : Nat)
    (hlen : xs.length = n) (f : α → β) :
    List.ofFn (fun i : Fin n => f (xs[i.val]'(by omega))) = xs.map f := by
  subst n
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (List.map f) (List.ofFn_getElem (xs := xs))

theorem projectDigest_words (d : Array Field 8#usize) :
    PublicRawCore.digestWords (projectDigest d) = d.val.map rawWord := by
  exact ofFn_map_getElem d.val 8 (by simpa using d.property) rawWord

theorem rows_eq_ofFn (f : Frontier431.Frontier) :
    Frontier431.rows f = List.ofFn (Frontier431.row f) := by
  simp only [Frontier431.rows, List.ofFn_succ, List.ofFn_zero]
  rfl

theorem frontierWords_agree (f : Frontier431.Frontier) :
    ((Frontier431.rows f).flatMap (fun s => s.val)).map rawWord =
      PublicRawCore.frontierWords (projectFrontier f) := by
  rw [rows_eq_ofFn, List.map_flatMap]
  simp only [PublicRawCore.frontierWords, List.flatMap_def, List.map_ofFn,
    Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact (projectDigest_words (f.val[i.val]'(by simpa [f.property] using i.isLt))).symm

theorem encodeWords_agree (xs : List Field) :
    (encodeWords xs).map rawByte = PublicRawCore.encodeWords (xs.map rawWord) := by
  simp only [encodeWords, PublicRawCore.encodeWords, List.map_flatMap, List.flatMap_map]
  exact congrArg (fun f => xs.flatMap f) (funext wordBytes_agree)

theorem core_encodeWords_append (xs ys : List PublicRawCore.Word) :
    PublicRawCore.encodeWords (xs ++ ys) =
      PublicRawCore.encodeWords xs ++ PublicRawCore.encodeWords ys := by
  exact List.flatMap_append

theorem rawByte_zero : rawByte 0#u8 = (0 : PublicRawCore.Byte) := rfl

theorem rawByte_one : rawByte 1#u8 = (1 : PublicRawCore.Byte) := rfl

theorem project_words (p : Public) :
    ((sourceSteps p).flatMap stepWords).map rawWord = PublicRawCore.words (project p) := by
  cases p <;>
    simp only [sourceSteps, tailSteps, stepWords, project, projectCommon,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.map_append, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
      PublicRawCore.words, PublicRawCore.headerWords, PublicRawCore.afterWords,
      projectDigest_words, ← frontierWords_agree, single, Array.to_slice, Array.make,
      List.append_assoc]

theorem project_bytes (p : Public) :
    ((sourceSteps p).flatMap stepBytes).map rawByte = PublicRawCore.encode (project p) := by
  cases p <;>
    simp only [sourceSteps, tailSteps, stepBytes, project, projectCommon,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.map_append, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
      encodeWords_agree, indexBytes_agree, frontierWords_agree,
      PublicRawCore.encode, PublicRawCore.afterBytes, PublicRawCore.headerWords,
      PublicRawCore.afterWords, core_encodeWords_append, projectDigest_words,
      single, Array.to_slice, Array.make, rawByte_zero, rawByte_one, List.append_assoc]

/-- Actual extracted success refines the fixed pure raw serializer. No field is
chosen from the output and no allocation/capacity premise is added. -/
theorem source_success_raw (p : Public) (out : ByteVec)
    (h : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p = ok (.Ok out)) :
    PublicRawCore.serialize (project p) = some (out.val.map rawByte) := by
  have hs := Whole431.source_success p out h
  have hc : PublicRawCore.Canonical (project p) := by
    intro x hx
    rw [← project_words] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hs.1 y hy
  have hb : out.val.map rawByte = PublicRawCore.encode (project p) := by
    rw [hs.2]
    exact project_bytes p
  simp only [PublicRawCore.serialize, if_pos hc, hb]

/-- This relation names the extracted Lean computation, not concrete Rust
runtime semantics. Its byte conversion and input projection are fixed above. -/
def ExtractedReturns (p : Public) (bytes : PublicRawCore.Bytes) : Prop :=
  ∃ out, pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p = ok (.Ok out) ∧
    out.val.map rawByte = bytes

theorem extracted_refines_core (p : Public) (bytes : PublicRawCore.Bytes)
    (h : ExtractedReturns p bytes) : PublicRawCore.serialize (project p) = some bytes := by
  obtain ⟨out, hs, rfl⟩ := h
  exact source_success_raw p out hs

#print axioms wordBytes_agree
#print axioms indexBytes_agree
#print axioms projectDigest_words
#print axioms rows_eq_ofFn
#print axioms frontierWords_agree
#print axioms encodeWords_agree
#print axioms project_words
#print axioms project_bytes
#print axioms source_success_raw
#print axioms extracted_refines_core

end AspisR1PublicSerializer.RawBridge431
