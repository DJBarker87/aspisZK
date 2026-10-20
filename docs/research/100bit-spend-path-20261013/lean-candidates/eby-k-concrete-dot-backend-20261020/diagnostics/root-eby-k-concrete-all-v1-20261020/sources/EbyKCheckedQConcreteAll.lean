import AspisR1EbyKCheckedQAllParamV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKCheckedQConcreteAll
open AspisR1EbyKCheckedQAllParamV1

/-- State-threaded, short-circuit all operational model; returned iterator
records the exact number of visited elements, including a rejected element. -/
def allRun (f : FnMutU32) : List U32 → Closure → Result (Bool × Nat)
  | [],_ => .ok (true,0)
  | x::xs,c => do
    let (b,c') ← f.call_mut c x
    if b then
      let (tail,n) ← allRun f xs c'
      .ok (tail,n+1)
    else .ok (false,1)

def concreteAll (f : FnMutU32) (it : IterU32) (c : Closure) : Result (Bool × IterU32) := do
  let (b,n) ← allRun f (it.slice.val.drop it.i) c
  .ok (b,{it with i:=it.i+n})

theorem selected_allRun_true (xs : List U32) (c : Closure) (n : Nat)
    (h : allRun fromLimbsClosureFnMut xs c = .ok (true,n)) :
    ∀ x ∈ xs, x.val < 2147483647 := by
  induction xs generalizing c n with
  | nil => simp
  | cons x xs ih =>
    change (do
      let (b,c') ← fromLimbsClosureCallMut c x
      if b then
        let (tail,k) ← allRun fromLimbsClosureFnMut xs c'
        .ok (tail,k+1)
      else .ok (false,1)) = .ok (true,n) at h
    simp only [fromLimbsClosureCallMut,bind_tc_ok] at h
    by_cases hp : x < P
    · rw [if_pos hp] at h
      cases htail : allRun fromLimbsClosureFnMut xs c with
      | ok pair =>
        rcases pair with ⟨b,k⟩
        rw [htail,bind_tc_ok] at h
        have hb : b=true := congrArg (fun q => q.1) (Result.ok.inj h)
        subst b
        have ht := ih c k htail
        intro y hy
        rcases List.mem_cons.mp hy with he|hy
        · subst y
          simpa only [P] using hp
        · exact ht y hy
      | fail e => simp only [htail,bind_tc_fail] at h;cases h
      | div => simp only [htail,bind_tc_div] at h;cases h
    · rw [if_neg hp] at h
      cases h

#print axioms selected_allRun_true
end AspisR1EbyKCheckedQConcreteAll
