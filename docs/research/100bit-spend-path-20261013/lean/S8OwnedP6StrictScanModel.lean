import S8OwnedP6Scan

set_option autoImplicit false
noncomputable section
namespace S8OwnedP6StrictScanModel
open Aeneas Aeneas.Std Result
open S8OwnedP6 S8OwnedP6Scan
open AspisR1.RetainedFieldByteCodec
open AspisR1.CandidateParserByteOrder

def CanonicalChunk (bytes : Slice U8) (j : Nat) : Prop :=
  ∃ arr : Array U8 16#usize, arr.val=(bytes.val.drop (16*j)).take 16 ∧
    (decodeQM31LE (arrayBytes16 arr)).isSome=true

/-- Good is the retained mathematical strict byte codec, rather than a free
interpretation of successful field decoding. -/
theorem good_iff_strict_codec (bytes : Slice U8) (j : Nat)
    (hj : j<bytes.val.length/16) : Good bytes j ↔ CanonicalChunk bytes j := by
  constructor
  · rintro ⟨s,hbytes,q,hq⟩
    have hsize : s.val.length=16 := by
      rw [hbytes,List.length_take,List.length_drop]
      have hb := S8OwnedP6LoopContracts.scan_offset_bounds bytes.val.length j hj
      omega
    let arr : Array U8 16#usize := ⟨s.val,by change s.val.length=16; exact hsize⟩
    have hs : Array.to_slice arr=s := by apply Subtype.ext; rfl
    have hp := AspisR1.S8OwnedP6StrictParser.source_refines arr
    rw [hs] at hp
    rw [hp] at hq
    refine ⟨arr,hbytes,?_⟩
    cases hd : decodeQM31LE (arrayBytes16 arr) with
    | none => simp only [hd,Option.map_none] at hq; cases hq
    | some limbs => rfl
  · rintro ⟨arr,hbytes,hcanonical⟩
    have hp := AspisR1.S8OwnedP6StrictParser.source_refines arr
    cases hd : decodeQM31LE (arrayBytes16 arr) with
    | none => simp only [hd,Option.isSome_none,Bool.false_eq_true] at hcanonical
    | some limbs =>
      refine ⟨Array.to_slice arr,hbytes,AspisR1.S8OwnedP6StrictParser.limbsToActual limbs,?_⟩
      simpa only [hd,Option.map_some] using hp

/-- Complete emitted strict compact scan equals the mathematical codec check
at every full chunk. Invalid bytes return NonCanonical, not a runtime failure. -/
theorem strict_scan_total (bytes : Slice U8) :
    ∃ out : Status, check_values_owned bytes=.ok out ∧
      (out=.Ok () ↔ ∀ j, j<bytes.val.length/16 → CanonicalChunk bytes j) ∧
      (out=.Ok () ∨ out=.Err .NonCanonical) := by
  obtain ⟨out,hrun,hequiv,hcases⟩ := scan_total_model bytes
  refine ⟨out,hrun,?_,hcases⟩
  rw [hequiv]
  constructor
  · intro h j hj; exact (good_iff_strict_codec bytes j hj).mp (h j hj)
  · intro h j hj; exact (good_iff_strict_codec bytes j hj).mpr (h j hj)

#print axioms good_iff_strict_codec
#print axioms strict_scan_total
end S8OwnedP6StrictScanModel
