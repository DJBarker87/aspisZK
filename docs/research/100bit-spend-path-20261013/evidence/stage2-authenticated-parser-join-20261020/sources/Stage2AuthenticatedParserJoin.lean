import Stage2AuthSuccess
import Stage2ParseShapeSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.Stage2AuthenticatedParserJoin
abbrev ParseVariant := AspisR1Stage2AdoptedParseShape.transport.Variant
abbrev CallerVariant := AspisR1Stage2AdoptedCaller.transport.Variant
abbrev ParseError := AspisR1Stage2AdoptedParseShape.verifier.Error
abbrev CallerError := AspisR1Stage2AdoptedCaller.verifier.Error

def mapVariant : ParseVariant → CallerVariant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

def mapError : ParseError → CallerError
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

/-- A field-preserving nominal type adapter between the two independently
extracted cuts of the same frozen Rust enum/result types. -/
def mappedParser (ops : AspisR1Stage2AdoptedParseShape.ParseShapeOps) (proof : Slice U8) :
    Result (core.result.Result CallerVariant CallerError) := do
  let r ← AspisR1Stage2AdoptedParseShape.verifier.candidate.parse_shape ops proof
  ok (match r with | .Ok v => .Ok (mapVariant v) | .Err e => .Err (mapError e))

def withParser {H : Type} (ops : AspisR1Stage2AdoptedParseShape.ParseShapeOps)
    (base : AspisR1Stage2AdoptedCaller.Stage2AuthBoundaries H) :
    AspisR1Stage2AdoptedCaller.Stage2AuthBoundaries H :=
  { base with parse_shape := mappedParser ops }

theorem mapped_success (ops : AspisR1Stage2AdoptedParseShape.ParseShapeOps)
    (proof : Slice U8) (variant : CallerVariant)
    (h : mappedParser ops proof = .ok (.Ok variant)) :
    AspisR1Stage2AdoptedParseShape.verifier.candidate.parse_shape ops proof = .ok (.Ok .S2) ∧
    variant = AspisR1Stage2AdoptedCaller.transport.Variant.S2 := by
  unfold mappedParser at h
  cases hp : AspisR1Stage2AdoptedParseShape.verifier.candidate.parse_shape ops proof with
  | fail e => simp [hp] at h
  | div => simp [hp] at h
  | ok result =>
    cases result with
    | Err e => simp [hp] at h
    | Ok v =>
      have hv := AspisR1Stage2AdoptedParseShape.ParseShapeSuccess.successful_variant ops proof v hp
      subst v
      exact ⟨rfl, by simpa [hp,mapVariant] using h.symm⟩

theorem authenticated_success_with_source_parser {H : Type}
    (ops : AspisR1Stage2AdoptedParseShape.ParseShapeOps)
    (base : AspisR1Stage2AdoptedCaller.Stage2AuthBoundaries H)
    (inst : AspisR1Stage2AdoptedCaller.aspis_core.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (AspisR1Stage2AdoptedCaller.verifier.Phase → Result Unit))
    (h : AspisR1Stage2AdoptedCaller.verifier.candidate.tx2_authenticated
        (withParser ops base) inst public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    AspisR1Stage2AdoptedParseShape.verifier.candidate.parse_shape ops proof = .ok (.Ok .S2) ∧
    AspisR1Stage2AdoptedParseShape.transport.Variant.tag .S2 = .ok 2#u8 ∧
    AspisR1Stage2AdoptedCaller.verifier.mark obs .Parsed = .ok () ∧
    base.tx2_common inst public_bytes proof checkpoint hash obs = .ok (.Ok ()) := by
  obtain ⟨variant,hparse,hmark,hcommon⟩ :=
    AspisR1Stage2AdoptedCaller.Stage2AuthSuccess.authenticated_success
      (withParser ops base) inst public_bytes proof checkpoint hash obs h
  have hp := mapped_success ops proof variant hparse
  exact ⟨hp.1,rfl,hmark,hcommon⟩
#print axioms mapped_success
#print axioms authenticated_success_with_source_parser
end AspisR1.Stage2AuthenticatedParserJoin
