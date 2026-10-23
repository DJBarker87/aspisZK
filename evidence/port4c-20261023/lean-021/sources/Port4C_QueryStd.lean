import Port4C_QueryValues
import OraclePortStdBuilder

/-! Install the existing TrustedStd ordered from_fn interpretation. It calls
all four native byte-decoder closures in order, with their original slice. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryStd
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
abbrev E := aspis_core.field.wide_exact.WideExact

def install (ops : Ops) : Ops :=
  {ops with op0 := OraclePortStdBuilder.fromFn}

def readValue (ops : Ops) (opening : Slice U8) (j : Usize) : Result E := do
  let values ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    opening {start:=672#usize,«end»:=800#usize}
  ops.op21 values j

theorem closure_exact (ops : Ops) (opening : Slice U8) (j : Usize) :
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (install ops) opening j = (do let value ← readValue ops opening j; ok (value,opening)) := by
  unfold verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut readValue
  simp only [bind_assoc_eq]

theorem indices_four : OraclePortStdBuilder.indices 4#usize=[0#usize,1#usize,2#usize,3#usize] := rfl

theorem four_reads (ops : Ops) (opening : Slice U8) (out : Array E 4#usize)
    (h : (install ops).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (install ops))
      opening=ok out) :
    ∃ v0 v1 v2 v3,
      readValue ops opening 0#usize=ok v0 ∧ readValue ops opening 1#usize=ok v1 ∧
      readValue ops opening 2#usize=ok v2 ∧ readValue ops opening 3#usize=ok v3 ∧
      out.val=[v0,v1,v2,v3] := by
  change OraclePortStdBuilder.fromFn 4#usize _ opening=ok out at h
  unfold OraclePortStdBuilder.fromFn at h
  rw [indices_four] at h
  simp only [OraclePortStdBuilder.fromFnLoop,
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact,
    closure_exact,bind_assoc_eq,bind_tc_ok] at h
  obtain ⟨v0,h0,h⟩ := bind_success _ _ _ h
  obtain ⟨v1,h1,h⟩ := bind_success _ _ _ h
  obtain ⟨v2,h2,h⟩ := bind_success _ _ _ h
  obtain ⟨v3,h3,h⟩ := bind_success _ _ _ h
  simp only [bind_tc_ok] at h
  cases Result.ok.inj h
  exact ⟨v0,v1,v2,v3,h0,h1,h2,h3,rfl⟩

#print axioms closure_exact
#print axioms indices_four
#print axioms four_reads
end AspisR1.Port4C_QueryStd
end
