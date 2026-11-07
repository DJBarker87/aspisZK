import NNG_ClosureFirst136
import NNG_ClosureSecond136
import NNG_FromFnOn136
set_option autoImplicit false
namespace AspisR1.NNG_FromFnValues136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Array136
open NNG_FromFnOn136 NNG_Offset16

def firstValue (claims : Claims) (i : Usize) : Q :=
  if hi : i.val < 16 then cell claims i (by omega) else cell claims 0#usize (by decide)
def secondValue (claims : Claims) (i : Usize) : Q :=
  if hi : i.val < 10 then cell claims (shifted i) (bound i hi) else cell claims 0#usize (by decide)

def low (claims : Claims) : Array Q 16#usize :=
  ⟨(OraclePortStdBuilder.indices 16#usize).map (firstValue claims), by
    rw [List.length_map, indices_length]⟩
def high (claims : Claims) : Array Q 10#usize :=
  ⟨(OraclePortStdBuilder.indices 10#usize).map (secondValue claims), by
    rw [List.length_map, indices_length]⟩

/-- Exact source from_fn for the first 16 mask inputs. Only visited indices
need the callback law; the captured Claims never changes. -/
theorem first {H : Type} (d : aspis_core.digest.Digest32 H) (claims : Claims) :
    NNG_StdArray.implementation 16#usize
      (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 d) claims =
      .ok (low claims) := by
  obtain ⟨value,returned,values⟩ := from_fn 16#usize
    (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 d)
    (firstValue claims) claims (by
      intro i hi
      have h16 : i.val < 16 := indices_bound 16#usize i hi
      change r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut d claims i = _
      rw [NNG_ClosureFirst136.source d claims i h16]
      simp only [firstValue, dif_pos h16])
  have same : value = low claims := Subtype.ext values
  exact returned.trans (congrArg Result.ok same)
#print axioms first

/-- Exact source from_fn for the ten mask inputs at indices 16..25. -/
theorem second {H : Type} (d : aspis_core.digest.Digest32 H) (claims : Claims) :
    NNG_StdArray.implementation 10#usize
      (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 d) claims =
      .ok (high claims) := by
  obtain ⟨value,returned,values⟩ := from_fn 10#usize
    (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 d)
    (secondValue claims) claims (by
      intro i hi
      have h10 : i.val < 10 := indices_bound 10#usize i hi
      change r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut d claims i = _
      rw [NNG_ClosureSecond136.source d claims i h10]
      simp only [secondValue, dif_pos h10])
  have same : value = high claims := Subtype.ext values
  exact returned.trans (congrArg Result.ok same)
#print axioms second
end AspisR1.NNG_FromFnValues136
