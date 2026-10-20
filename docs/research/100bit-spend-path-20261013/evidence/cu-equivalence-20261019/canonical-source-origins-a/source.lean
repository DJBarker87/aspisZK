import CuSavingsCanonicalDotsInvariant
import CuSavingsCanonicalInputParser
import CuSavingsCanonicalSampler
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsSources
open Aeneas Aeneas.Std Result
abbrev I := AspisR1CanonicalInputs.field.wide_exact.WideExact
abbrev D := AspisR1CanonicalDots.field.wide_exact.WideExact
abbrev S := AspisR1CanonicalSampler.field.wide_exact.WideExact

def inputToDot (x : I) : D :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def dotToInput (x : D) : I :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def sampleToInput (x : S) : I :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem input_canonical (x : I) (h : CuSavingsCanonicalInputPowers.Canonical x) :
    CuSavingsCanonicalDotsField.WideCanonical (inputToDot x) := by
  rcases h with ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨⟨he,hf⟩,⟨hg,hh⟩⟩⟩
  exact ⟨⟨ha,hb,hc,hd⟩,⟨he,hf,hg,hh⟩⟩

theorem dot_canonical (x : D) (h : CuSavingsCanonicalDotsField.WideCanonical x) :
    CuSavingsCanonicalInputPowers.Canonical (dotToInput x) := by
  rcases h with ⟨⟨ha,hb,hc,hd⟩,⟨he,hf,hg,hh⟩⟩
  exact ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨⟨he,hf⟩,⟨hg,hh⟩⟩⟩

theorem sample_canonical (x : S) (h : CuSavingsCanonicalSampler.Canonical x) :
    CuSavingsCanonicalInputPowers.Canonical (sampleToInput x) := by
  rcases h with ⟨⟨ha,hb,hc,hd⟩,⟨he,hf,hg,hh⟩⟩
  exact ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨⟨he,hf⟩,⟨hg,hh⟩⟩⟩

variable [AspisR1CanonicalSampler.Shared]
/-- Actual-source value origins at the private accumulator boundary. These
constructors record executions of the real source producers, not validity
assumptions about arbitrary WideExact records. -/
inductive SourceValue : I→Prop
  | sampled {H : Type} (digest : AspisR1CanonicalSampler.Digest32 H)
      (self after : AspisR1CanonicalSampler.transcript.Transcript H)
      (row : U8) (payload : Slice U8) (nonzero : Bool) (value : S)
      (h : AspisR1CanonicalSampler.transcript.Transcript.scalar digest self row payload nonzero=
        .ok (value,after)) : SourceValue (sampleToInput value)
  | decoded (bytes : Slice U8) (index : Usize) (value : I)
      (h : AspisR1CanonicalInputs.weights.field bytes index=.ok value) : SourceValue value
  | finished (self : AspisR1CanonicalDots.old_pairing.EbyKDot) (value : D)
      (h : AspisR1CanonicalDots.old_pairing.EbyKDot.finish self=.ok value) :
      SourceValue (dotToInput value)
  | power (N : Usize) (base : I) (values : Array I N) (index : Nat)
      (hi : index<N.val) (hb : SourceValue base)
      (h : AspisR1CanonicalInputs.weights.powers N base=.ok values) :
      SourceValue (values.val[index]'(by rw [values.property];exact hi))

theorem source_canonical (value : I) (h : SourceValue value) :
    CuSavingsCanonicalInputPowers.Canonical value := by
  induction h with
  | sampled digest self after row payload nonzero value hs =>
      exact sample_canonical value (CuSavingsCanonicalSampler.scalar_success
        digest self after row payload nonzero value hs)
  | decoded bytes index value hd => exact CuSavingsCanonicalInputParser.field_success bytes index value hd
  | finished self value hf =>
      have heq := Result.ok.inj ((CuSavingsCanonicalDotsFinish.old_public_finish self).symm.trans hf)
      cases heq
      exact dot_canonical _ (CuSavingsCanonicalDotsFinish.result_canonical _ _)
  | power N base values index hi hb hp ih =>
      obtain ⟨out,hr,hc⟩ := CuSavingsCanonicalInputPowers.source_success N base ih
      have heq := Result.ok.inj (hr.symm.trans hp)
      cases heq
      exact (hc index hi).1

variable [AspisR1CanonicalDots.Shared]
inductive SourceState : AspisR1CanonicalDots.old_pairing.EbyKDot→Prop
  | initial : SourceState CuSavingsCanonicalDotsInvariant.initial
  | pushed (self out : AspisR1CanonicalDots.old_pairing.EbyKDot)
      (value : I) (scalar : AspisR1CanonicalDots.field.QM31)
      (hs : SourceState self) (hv : SourceValue value)
      (h : AspisR1CanonicalDots.old_pairing.EbyKDot.push self (inputToDot value) scalar=
        .ok (.Ok (),out)) : SourceState out

theorem source_counts (state : AspisR1CanonicalDots.old_pairing.EbyKDot)
    (h : SourceState state) : CuSavingsCanonicalDotsPush.RelatedCounts state := by
  induction h with
  | initial => exact CuSavingsCanonicalDotsInvariant.initial_counts
  | pushed self out value scalar hs hv hp ih =>
      exact CuSavingsCanonicalDotsInvariant.push_counts self out (inputToDot value) scalar
        (input_canonical value (source_canonical value hv)) ih hp

theorem source_push_equivalence (state : AspisR1CanonicalDots.old_pairing.EbyKDot)
    (hs : SourceState state) (value : I) (hv : SourceValue value)
    (scalar : AspisR1CanonicalDots.field.QM31) :
    AspisR1CanonicalDots.new_pairing.EbyKDot.push (CuSavingsCanonicalDotsPush.project state)
      (inputToDot value) scalar =
    (AspisR1CanonicalDots.old_pairing.EbyKDot.push state (inputToDot value) scalar >>=
      fun out=>.ok (CuSavingsCanonicalDotsPush.projectResult out)) :=
  CuSavingsCanonicalDotsPush.public_push state (inputToDot value) scalar
    (input_canonical value (source_canonical value hv)) (source_counts state hs)

#print axioms input_canonical
#print axioms dot_canonical
#print axioms sample_canonical
#print axioms source_canonical
#print axioms source_counts
#print axioms source_push_equivalence
end AspisR1.CuSavingsCanonicalDotsSources
