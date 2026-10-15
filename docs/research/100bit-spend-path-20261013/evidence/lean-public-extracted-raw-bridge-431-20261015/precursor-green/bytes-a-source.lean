import PublicSerializerWhole431
import PublicRawCore

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

#print axioms wordBytes_agree
#print axioms indexBytes_agree

end AspisR1PublicSerializer.RawBridge431
