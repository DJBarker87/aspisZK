import AspisR1S9PairCallerStepV1.Funs
import S9PairCallerCandidateMapV1
import S9CandidateFoldMapPrimitivesV1
import S9HighTermsTraceV1
import S9PairMixedCallToSourceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedInputCanonicalV1

abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PairArray := Array PairW (4#usize)
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev U := Std.Usize
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev ToP6W := AspisR1S9CandidateHelperV1.toP6W

private def pairToCurrentCM (x : AspisR1S9PairCallerStepV1.field.CM31) :
    AspisR1CurrentWide.field.CM31 := ⟨x.a, x.b⟩
private def pairToCurrentQ (x : PairQ) : AspisR1CurrentWide.field.QM31 :=
  ⟨pairToCurrentCM x.c0, pairToCurrentCM x.c1⟩
def pairToCurrentW (x : PairW) : AspisR1CurrentWide.field.wide_exact.WideExact :=
  ⟨pairToCurrentQ x.c0, pairToCurrentQ x.c1⟩

/-- A successful Pair array read inherits exactly the public mapped-input
canonicality contract, transported to the CurrentWide carrier used by the
mixed-product source map. -/
theorem pair_read_current_canonical
    (ap1 : PairArray) (i : U) (x : PairW)
    (hread : Array.index_usize ap1 i = .ok x)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    AspisR1CurrentWide.Proof.CanonicalWide (pairToCurrentW x) := by
  have hm1 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    PairMapW ap1 i
  rw [hread] at hm1
  change .ok (PairMapW x) = Array.index_usize (mapArray PairMapW ap1) i at hm1
  have hm1' : Array.index_usize (mapArray PairMapW ap1) i = .ok (PairMapW x) := hm1.symm
  have hm2 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    ToP6W (mapArray PairMapW ap1) i
  rw [hm1'] at hm2
  simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hm2
  have hm2' : Array.index_usize (mapArray ToP6W (mapArray PairMapW ap1)) i =
      .ok (ToP6W (PairMapW x)) := hm2.symm
  have hc := hap1 i (ToP6W (PairMapW x)) hm2'
  have hcarrier :
      AspisR1S9GeneratedWideMulQM31V2.toWide (ToP6W (PairMapW x)) = pairToCurrentW x := by
    change AspisR1S9GeneratedWideMulQM31V2.toWide
      (AspisR1S9CandidateHelperV1.toP6W
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW x)) = pairToCurrentW x
    rw [AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW]
    cases x <;> rfl
  rw [← hcarrier]
  exact hc

/-- Same-call source transport for a mixed product at a left operand read from
`ap1`. The canonicality obligation is discharged from the same successful
array read and the public mapped-input contract. -/
theorem pair_read_mixed_call_maps_to_source
    (ap1 : PairArray) (i : U) (x : PairW) (q : PairQ)
    (hread : Array.index_usize ap1 i = .ok x)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q =
      AspisR1S9PairMixedCallToSourceV1.mapResult
        AspisR1S9PairMixedCallToSourceV1.srcToPairW
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
          (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)
          (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ q)) := by
  apply AspisR1S9PairMixedCallToSourceV1.pair_mul_qm31_eq_source
  exact pair_read_current_canonical ap1 i x hread hap1

/-- The reflected source success is for the exact caller bind witness supplied
by the enclosing afterLow execution. Thus callers can retain the very same
`x`, `q`, and `out` obtained by bind inversion. -/
theorem pair_read_mixed_call_success_reflects_source
    (ap1 : PairArray) (i : U) (x : PairW) (q : PairQ) (out : PairW)
    (hread : Array.index_usize ap1 i = .ok x)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v)
    (hcall : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q = .ok out) :
    ∃ sourceOut,
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ q) = .ok sourceOut ∧
      out = AspisR1S9PairMixedCallToSourceV1.srcToPairW sourceOut := by
  apply AspisR1S9PairMixedCallToSourceV1.pair_mul_qm31_success_reflects_source
    x q out (pair_read_current_canonical ap1 i x hread hap1)
  exact hcall

#print axioms pair_read_current_canonical
#print axioms pair_read_mixed_call_maps_to_source
#print axioms pair_read_mixed_call_success_reflects_source

end AspisR1S9PairMixedInputCanonicalV1
