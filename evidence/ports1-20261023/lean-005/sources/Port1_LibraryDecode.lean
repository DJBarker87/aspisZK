import Port1_LibrarySource
import UnrolledWideParserRefinement

/-! Symbolic carrier transport, preserving all eight canonicality guards.
No concrete field enumeration or recurrence reduction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_LibraryDecode
open Aeneas Aeneas.Std Result VTop_Stages Port1_LibrarySource

def cm (x : AspisR1CandidateParser.field.CM31) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def qm (x : AspisR1CandidateParser.field.QM31) : aspis_core.field.QM31 := ⟨cm x.c0,cm x.c1⟩
def wide (x : AspisR1CandidateParser.field.wide_exact.WideExact) :
    aspis_core.field.wide_exact.WideExact := ⟨qm x.c0,qm x.c1⟩

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x) | .fail e => .fail e | .div => .div

theorem map_bind {A B C : Type} (f : B → C) (m : Result A) (k : A → Result B) :
    mapResult f (m >>= k) = (m >>= fun x => mapResult f (k x)) := by
  cases m <;> rfl

theorem map_ite {A B : Type} (f : A → B) (p : Prop) [Decidable p] (a b : Result A) :
    mapResult f (if p then a else b) = if p then mapResult f a else mapResult f b := by
  split <;> rfl

theorem limbs_agreement (limbs : Array U32 8#usize) :
    mapResult (Option.map wide)
      (AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled limbs) =
      fromLimbs limbs := by
  unfold AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled
    fromLimbs AspisR1CandidateParser.field.P
  simp only [map_bind, map_ite]
  rfl

theorem decoder_agreement (bytes : Slice U8) :
    mapResult (Option.map wide)
      (AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes) =
      decode bytes := by
  unfold AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
    decode AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN
  simp only [map_ite, map_bind, limbs_agreement]
  rfl

theorem strict_fixed (bytes : Array U8 32#usize) :
    decode (Array.to_slice bytes) = .ok
      ((StrictWideByteCodec.decodeWideLE (WideParserArrayHalves.arrayBytes32 bytes)).map
        (fun x => wide (CandidateWideParserRefinement.limbsToCandidate x))) := by
  rw [← decoder_agreement, UnrolledWideParserRefinement.source_refines]
  simp only [mapResult, Option.map_map]

theorem wrong_length (bytes : Slice U8) (length : bytes.val.length ≠ 32) :
    decode bytes = .ok none := by
  rw [← decoder_agreement, UnrolledWideByteReads.wrong_length bytes length]
  rfl

#print axioms map_bind
#print axioms map_ite
#print axioms limbs_agreement
#print axioms decoder_agreement
#print axioms strict_fixed
#print axioms wrong_length
end AspisR1.Port1_LibraryDecode
end
