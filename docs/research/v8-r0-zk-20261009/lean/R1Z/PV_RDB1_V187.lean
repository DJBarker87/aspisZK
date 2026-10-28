import R1Z.PV_RDB1_V187Iterator
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V187

def value {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    core.result.Result (Array T N) (alloc.vec.Vec T) :=
  if h : v.val.length=N.val then .Ok ⟨v.val,h⟩ else .Err v

/-- Bulk read after set_len(0), followed by empty-Vec drop. finish carries the
same retained allocation identity/capacity/allocator into deallocation glue.
All Result variants of that primitive remain visible. -/
def deployed {T W : Type} (N : Usize) (v : alloc.vec.Vec T) (w : W)
    (finish : W → Result W) :
    Result (core.result.Result (Array T N) (alloc.vec.Vec T) × W) :=
  if h : v.val.length=N.val then do
    let w' ← finish w
    ok (.Ok ⟨v.val,h⟩,w')
  else ok (.Err v,w)

/-- Actual forward fill order; short-iterator panic and initialized-array
length check are explicit. On the admitted length branch both are discharged
by fill_exact, before interpreting destructor/deallocator effects. -/
def reference {T W : Type} (N : Usize) (v : alloc.vec.Vec T) (w : W)
    (finish : W → Result W) :
    Result (core.result.Result (Array T N) (alloc.vec.Vec T) × W) :=
  if v.val.length=N.val then do
    let (owned, remaining) ← PV_RDB1_V187Iterator.fill N.val v.val []
    (if h : owned.length=N.val then do
      let w' ← finish w
      ok (.Ok ⟨owned,h⟩,w')
    else fail .panic)
  else ok (.Err v,w)

theorem complete {T W : Type} (N : Usize) (v : alloc.vec.Vec T) (w : W)
    (finish : W → Result W) : reference N v w finish = deployed N v w finish := by
  by_cases h : v.val.length=N.val
  · simp only [reference,deployed,if_pos h,dif_pos h]
    have hf : PV_RDB1_V187Iterator.fill N.val v.val [] = ok (v.val,[]) := by
      rw [← h,PV_RDB1_V187Iterator.complete]
    rw [hf]
    simp only [bind_tc_ok,Aeneas.Std.uncurry,dif_pos h]
  · simp only [reference,deployed,if_neg h,dif_neg h]

/-- Exact old op36 value carrier and quantifiers, with generic effects still
visible before projection. No Copy, Clone, Inhabited or success hypothesis. -/
theorem value_result {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    (do let (out,_) ← reference N v () (fun _ => ok ()); ok out) = ok (value N v) := by
  rw [complete]
  by_cases h : v.val.length=N.val
  · simp only [deployed,value,dif_pos h,bind_tc_ok,Aeneas.Std.uncurry]
  · simp only [deployed,value,dif_neg h,bind_tc_ok,Aeneas.Std.uncurry]

theorem rejected_world {T W : Type} (N : Usize) (v : alloc.vec.Vec T) (w : W)
    (finish : W → Result W) (h : v.val.length ≠ N.val) :
    reference N v w finish = ok (.Err v,w) := by
  rw [complete]
  simp only [deployed,dif_neg h]

/-- Finalization occurs only after all live T have transferred. There is no
remaining payload destructor; finish's allocator state/effect is not erased. -/
theorem successful_world {T W : Type} (N : Usize) (v : alloc.vec.Vec T) (w : W)
    (finish : W → Result W) (h : v.val.length=N.val) :
    reference N v w finish =
      (do let w' ← finish w; ok (.Ok (⟨v.val,h⟩ : Array T N),w')) := by
  rw [complete]
  simp only [deployed,dif_pos h]

#print axioms complete
#print axioms value_result
#print axioms rejected_world
#print axioms successful_world
end R1Z.PV_RDB1_V187
