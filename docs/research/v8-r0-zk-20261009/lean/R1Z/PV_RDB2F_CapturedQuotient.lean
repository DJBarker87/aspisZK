import R1Z.PV_RDB2F_Digits
namespace R1Z.PV_RDB2F_CapturedQuotient
open Aeneas Aeneas.Std Result ControlFlow PV_RDB2F_Iterator
set_option autoImplicit false
/-- The original FnMut loan returns both its digit and its mutated captured quotient. -/
def invoke (captured : Words) : Result (U32 × Words) := do
  let (current,remainder) ← division captured 0#u64 8#usize
  let digit ← lift (UScalar.cast .U32 remainder)
  ok (digit,current)
/-- Guard::push_unchecked writes the returned item before incrementing initialized. -/
def guardBody (captured output : Words) (initialized : Usize) :
    Result (ControlFlow (Words × Words × Usize) (Words × Words)) := do
  if initialized < 8#usize then
    let (item,current) ← invoke captured
    let storage ← Array.update output initialized item
    let count ← lift (Usize.wrapping_add initialized 1#usize)
    ok (cont (current,storage,count))
  else ok (done (captured,output))

theorem body_association (q output : Words) (initialized : Usize) :
    guardBody q output initialized=digitsBody q output initialized := by
  simp only [guardBody,invoke,digitsBody,bind_assoc_eq,bind_tc_ok]

def fromFn (q output : Words) (initialized : Usize) : Result (Words × Words) :=
  loop (fun (q,output,initialized) => guardBody q output initialized) (q,output,initialized)

theorem entire_capture (q output : Words) (initialized : Usize) :
    fromFn q output initialized=digits q output initialized := by
  unfold fromFn digits
  have e : (fun (q,ds,i) => guardBody q ds i)=(fun (q,ds,i) => digitsBody q ds i) := by
    funext ⟨q,ds,i⟩;exact body_association q ds i
  rw [e]

theorem final_capture_read (q output : Words) :
    (do let (current,_) ← fromFn q output 0#usize
        Array.index_usize current 0#usize)=
    (do let (current,_) ← digits q output 0#usize
        Array.index_usize current 0#usize) := by rw [entire_capture]

#print axioms body_association
#print axioms entire_capture
#print axioms final_capture_read
end R1Z.PV_RDB2F_CapturedQuotient
