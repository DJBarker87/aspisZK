import AspisR1RhoReader.Funs
import CuSavingsRhoParserCanonicality
import CuSavingsRhoInitRow

/-! Successful actual checkpoint reads establish canonical words and the
actual reader frame/advance. No assumption that decoding succeeds is made.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoReader
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem parser_success (bytes : Slice U8) (q : field.QM31)
    (h : field.QM31.from_le_bytes bytes = .ok (some q)) : Canonical q := by
  have hc := CuSavingsRhoParserCanonicality.qm31_from_le_bytes_success_canonical bytes q h
  have hp : field.P.val = AspisV8R17.RawReducer.P := by rw [field.P];rfl
  intro j
  fin_cases j
  · change q.c0.a.val < AspisV8R17.RawReducer.P
    rw [← hp]
    exact hc.1
  · change q.c0.b.val < AspisV8R17.RawReducer.P
    rw [← hp]
    exact hc.2.1
  · change q.c1.a.val < AspisV8R17.RawReducer.P
    rw [← hp]
    exact hc.2.2.1
  · change q.c1.b.val < AspisV8R17.RawReducer.P
    rw [← hp]
    exact hc.2.2.2

theorem raw_success (length : Usize) (self out : verifier.Reader)
    (bytes : Array U8 length) (h : verifier.Reader.raw length self = .ok (bytes,out)) :
    out.bytes=self.bytes ∧ out.«at».val=self.«at».val+length.val := by
  unfold verifier.Reader.raw at h
  obtain ⟨index,hadd,h⟩ := bind_ok _ _ _ h
  have hv := UScalar.add_equiv self.«at» length
  rw [hadd] at hv
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  have heq := congrArg Prod.snd (Result.ok.inj h)
  change ({self with «at»:=index} : verifier.Reader) = out at heq
  rw [← heq]
  exact ⟨rfl,hv.2.1⟩

theorem k_success (self out : verifier.Reader) (q : field.QM31)
    (h : verifier.Reader.k self = .ok (.Ok q,out)) :
    Canonical q ∧ out.bytes=self.bytes ∧ out.«at».val=self.«at».val+16 := by
  unfold verifier.Reader.k at h
  obtain ⟨pair,hraw,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨bytes,reader⟩
  simp only [uncurry_apply_pair,lift,bind_tc_ok] at h
  obtain ⟨parsed,hparse,h⟩ := bind_ok _ _ _ h
  cases parsed with
  | none =>
    simp only [AspisR1CuRho.core.option.Option.ok_or,bind_tc_ok] at h
    cases h
  | some value =>
    simp only [AspisR1CuRho.core.option.Option.ok_or,bind_tc_ok] at h
    have hc := parser_success _ value hparse
    have hr := raw_success 16#usize self reader bytes hraw
    have heq := Result.ok.inj h
    cases heq
    exact ⟨hc,hr.1,by simpa only [show (16#usize).val=16 by scalar_tac] using hr.2⟩

theorem k_outcome (self : verifier.Reader) :
    verifier.Reader.k self = (do
      let (bytes,reader) ← verifier.Reader.raw 16#usize self
      let parsed ← field.QM31.from_le_bytes (Array.to_slice bytes)
      match parsed with
      | none => .ok (.Err verifier.Error.Checkpoint,reader)
      | some q => .ok (.Ok q,reader)) := by
  unfold verifier.Reader.k
  cases hr : verifier.Reader.raw 16#usize self with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨bytes,reader⟩
    simp only [bind_tc_ok,uncurry_apply_pair,lift]
    cases hp : field.QM31.from_le_bytes (Array.to_slice bytes) with
    | fail error => rfl
    | div => rfl
    | ok parsed => cases parsed <;> rfl

/-- The inherited opaque Formatter type occurs only through this unused Debug
argument. No formatter property or equivalence proposition is postulated. -/
theorem unwrap_debug_unused {T E : Type} (left right : core.fmt.Debug E)
    (value : core.result.Result T E) :
    core.result.Result.unwrap left value = core.result.Result.unwrap right value := rfl

#print core.fmt.Formatter
#print axioms k_outcome
#print axioms unwrap_debug_unused

#print axioms parser_success
#print axioms raw_success
#print axioms k_success
end AspisR1.CuSavingsRhoReader
