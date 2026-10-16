import AspisR1EcheckCut.Funs
import UnrolledWideParserSource

/-! Carrier transport from the source-extracted echeck parser to the retained
Candidate Wide parser. The echeck side is the namespace-renamed generated
module from the exact Aeneas output; only the outer namespace is adapted so its
WideExact does not collide with the selected-mask extraction. The function
bodies are copied from the pinned generated Funs output (see source pins in the
accompanying echeck extraction bundle). -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralRow30ParserAgreement
open Aeneas Aeneas.Std Result

abbrev EcheckWide := AspisR1EcheckCut.field.wide_exact.WideExact
abbrev CandidateWide := AspisR1CandidateParser.field.wide_exact.WideExact

def m31ToCandidate (x : AspisR1EcheckCut.field.M31) :
    AspisR1CandidateParser.field.M31 := x

def cmToCandidate (x : AspisR1EcheckCut.field.CM31) :
    AspisR1CandidateParser.field.CM31 :=
  ⟨m31ToCandidate x.a, m31ToCandidate x.b⟩

def qmToCandidate (x : AspisR1EcheckCut.field.QM31) :
    AspisR1CandidateParser.field.QM31 :=
  ⟨cmToCandidate x.c0, cmToCandidate x.c1⟩

def wideToCandidate (x : EcheckWide) : CandidateWide :=
  ⟨qmToCandidate x.c0, qmToCandidate x.c1⟩

def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | ok x => ok (f x)
  | fail e => fail e
  | div => div

theorem mapResult_bind {α β γ : Type} (f : β → γ)
    (m : Result α) (k : α → Result β) :
    mapResult f (m >>= k) = (m >>= fun x => mapResult f (k x)) := by
  cases m <;> rfl

theorem mapResult_ite {α β : Type} (f : α → β)
    (p : Prop) [Decidable p] (a b : Result α) :
    mapResult f (if p then a else b) =
      if p then mapResult f a else mapResult f b := by
  split <;> rfl

@[simp] theorem mapResult_ok {α β : Type} (f : α → β) (x : α) :
    mapResult f (ok x) = ok (f x) := rfl

theorem from_limbs_agreement (limbs : Array U32 8#usize) :
    mapResult (Option.map wideToCandidate)
      (AspisR1EcheckCut.field.wide_exact.WideExact.from_limbs limbs) =
      AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled limbs := by
  unfold AspisR1EcheckCut.field.wide_exact.WideExact.from_limbs
    AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled
    AspisR1EcheckCut.field.P AspisR1CandidateParser.field.P
  simp only [mapResult_bind, mapResult_ite, mapResult_ok,
    Option.map_none, Option.map_some]
  rfl

theorem from_le_bytes_agreement (bytes : Slice U8) :
    mapResult (Option.map wideToCandidate)
      (AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes := by
  unfold AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
    AspisR1EcheckCut.field.wide_exact.WideExact.BYTE_LEN
    AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN
  simp only [mapResult_ite, mapResult_bind, mapResult_ok,
    Option.map_none, from_limbs_agreement]

theorem actual_success_to_candidate_success (bytes : Slice U8)
    (w : EcheckWide)
    (h : AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes bytes =
      ok (some w)) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes =
      ok (some (wideToCandidate w)) := by
  have hm := congrArg (mapResult (Option.map wideToCandidate)) h
  rw [from_le_bytes_agreement] at hm
  exact hm

#print axioms from_limbs_agreement
#print axioms from_le_bytes_agreement
#print axioms actual_success_to_candidate_success

end AspisR1.CanonicalLiteralRow30ParserAgreement
