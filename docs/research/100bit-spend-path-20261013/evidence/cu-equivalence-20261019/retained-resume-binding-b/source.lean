import CuSavingsRetainedResumeCells
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeBinding
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
open CuSavingsRetainedResumeOrigins
structure Queries where
  r : ResumeReader
  queries : Array U32 22#usize
structure Tail where
  r : ResumeReader
  z : Array aspis_core.circle.SecureCirclePoint 2#usize
  claim : aspis_core.field.WideExact
  rhs : aspis_core.field.WideExact
/-- Exact unchanged source fragments: authenticated header/state/roots;
queries/checks; and point/claim/rhs reads. None receives retained decoded
alpha/gamma/semantic_alpha values. No successful execution law is assumed. -/
structure Boundaries where
  header : {H : Type} → aspis_core.Digest32 H → Slice U8 → Slice U8 → Slice U8 → transport.Variant → H → Result (core.result.Result ResumeHeader verifier.Error)
  queries : ResumeReader → Result (core.result.Result Queries verifier.Error)
  tail : ResumeReader → Result (core.result.Result Tail verifier.Error)
  allocationBackend : CuSavingsRhoEmptyReserveModel.Backend

variable [AspisR1CanonicalReader.Runtime]
def beginSource (B : Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (bytes proof publicValue : Slice U8) (variant : transport.Variant) (hash : H) :
    Result (core.result.Result ResumeBegin verifier.Error) := do
  let header ← B.header D bytes proof publicValue variant hash
  match header with
  | .Err error => .ok (.Err error)
  | .Ok header => retained_begin_fields header

def middleSource (B : Boundaries) (r : ResumeReader) : Result (core.result.Result ResumeMiddle verifier.Error) := do
  let queries ← B.queries r
  match queries with
  | .Err error => .ok (.Err error)
  | .Ok queries =>
    let values ← CuSavingsRetainedResumeCells.cells (10#usize).val queries.r
    match values with
    | .Err error => .ok (.Err error)
    | .Ok (values,r1) =>
      let tail ← B.tail r1
      match tail with
      | .Err error => .ok (.Err error)
      | .Ok tail => .ok (.Ok {r:=tail.r,queries:=queries.queries,semantic_alpha:=⟨values.val,values.property⟩,z:=tail.z,claim:=tail.claim,rhs:=tail.rhs})

@[reducible] def binding (B : Boundaries) : ResumeCommon :=
  {beginSource:=beginSource B,middleSource:=middleSource B,allocationBackend:=B.allocationBackend}

private theorem bind_ok {A C : Type} (m : Result A) (f : A→Result C) (out : C)
    (h : (m >>= f)=.ok out) : ∃ x,m=.ok x ∧ f x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalKReader.Runtime]
theorem begin_success (B : Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (bytes proof publicValue : Slice U8) (variant : transport.Variant) (hash : H) (out : ResumeBegin)
    (h : beginSource B D bytes proof publicValue variant hash=.ok (.Ok out)) :
    ReaderOrigin out.gamma ∧ ∃ a0 a1,out.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (libra a0) ∧ CuSavingsLibraOrigins.Alpha (libra a1) := by
  unfold beginSource at h
  obtain ⟨header,_,h⟩ := bind_ok _ _ _ h
  cases header with
  | Err e => cases h
  | Ok header => exact CuSavingsRetainedResumeOrigins.begin_success header out h

theorem middle_success (B : Boundaries) (r : ResumeReader) (out : ResumeMiddle)
    (h : middleSource B r=.ok (.Ok out)) :
    ∀ (i : Nat) (hi : i<out.semantic_alpha.val.length),
      CuSavingsRhoInitRow.Canonical (out.semantic_alpha.val[i]'hi) := by
  unfold middleSource at h
  obtain ⟨queries,_,h⟩ := bind_ok _ _ _ h
  cases queries with
  | Err e => cases h
  | Ok queries =>
    obtain ⟨values,hv,h⟩ := bind_ok _ _ _ h
    cases values with
    | Err e => cases h
    | Ok pair =>
      rcases pair with ⟨values,r1⟩
      simp only [uncurry_apply_pair] at h
      have hc := CuSavingsRetainedResumeCells.source_success _ queries.r r1 values hv
      obtain ⟨tail,_,h⟩ := bind_ok _ _ _ h
      cases tail with
      | Err e => cases h
      | Ok tail =>
        cases core.result.Result.Ok.inj (Result.ok.inj h)
        intro i hi
        exact hc _ (List.getElem_mem hi)

#print axioms begin_success
#print axioms middle_success
end AspisR1.CuSavingsRetainedResumeBinding
