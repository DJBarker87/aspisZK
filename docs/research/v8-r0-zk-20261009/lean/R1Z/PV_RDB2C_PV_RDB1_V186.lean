import Aeneas

/-! V186 deployed structural link. The native Default body and the retained
owned Rust reference are each exactly `Vec::new()`. Treat the shared constructor
as arbitrary: no old sysroot law or allocation/failure hypothesis is transported.
The source gate binds these two expressions, including their selected callee.
This is a library source correspondence, not a compiler/machine theorem. -/
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V186

def defaultCall {α : Type} (newCall : Result α) : Result α := newCall

def referenceCall {α : Type} (newCall : Result α) : Result α := newCall

theorem complete {α : Type} (newCall : Result α) :
    defaultCall newCall = referenceCall newCall := rfl

/-- Exact existing op35 result, with no premise about a historical sysroot. -/
theorem selected_result (T : Type) :
    defaultCall (ok (alloc.vec.Vec.new T)) =
    ok (alloc.vec.Vec.new T) := rfl

/-- The changed dangling pointer/capacity representation cannot affect the
value carrier of an empty native Vec: zero live length forces its list empty. -/
theorem empty_from_zero_length {T : Type} (v : alloc.vec.Vec T)
    (h : v.val.length = 0) : v = alloc.vec.Vec.new T := by
  apply Subtype.ext
  exact List.eq_nil_of_length_eq_zero h

theorem constructor_value (T : Type) :
    (alloc.vec.Vec.new T).val = [] := rfl

#print axioms empty_from_zero_length
#print axioms constructor_value
#print axioms complete
#print axioms selected_result
end R1Z.PV_RDB1_V186
