import R1Z.PV_RDB2E_FromFn
namespace R1Z.PV_RDB2F_FromFnGuard
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- Initialized filled of Guard::array_mut. The same FnMut state is passed on. -/
def guarded {S A : Type} (f : Nat → S → Result (A × S)) :
    Nat → Nat → List A → S → Result (List A × S)
  | 0,_,filled,s => ok (filled,s)
  | n+1,i,filled,s => do
      let (item,current) ← f i s
      guarded f n (i+1) (filled++[item]) current

theorem initialized_prefix {S A : Type} (f : Nat → S → Result (A × S))
    (n i : Nat) (filled : List A) (s : S) :
    guarded f n i filled s =
      (do let (tail,after) ← PV_RDB2E_FromFn.build f n i s
          ok (filled++tail,after)) := by
  induction n generalizing i filled s with
  | zero => simp [guarded,PV_RDB2E_FromFn.build,bind_tc_ok]
  | succ n ih =>
    cases hf : f i s with
    | fail e => simp [guarded,PV_RDB2E_FromFn.build,hf]
    | div => simp [guarded,PV_RDB2E_FromFn.build,hf]
    | ok pair =>
      rcases pair with ⟨item,current⟩
      simp only [guarded,PV_RDB2E_FromFn.build,hf,bind_tc_ok]
      change guarded f n (i+1) (filled++[item]) current = _
      rw [ih]
      cases hb : PV_RDB2E_FromFn.build f n (i+1) current with
      | fail e => simp [hb,bind_tc_fail]
      | div => simp [hb,bind_tc_div]
      | ok pair =>
        rcases pair with ⟨tail,after⟩
        simp [hb,bind_tc_ok,List.append_assoc]

theorem complete_capture {S A : Type} (f : Nat → S → Result (A × S))
    (n : Nat) (s : S) :
    guarded f n 0 [] s=PV_RDB2E_FromFn.build f n 0 s := by
  rw [initialized_prefix]
  simp only [List.nil_append]
  cases PV_RDB2E_FromFn.build f n 0 s <;> rfl

theorem store_before_increment (initialized : Nat) (filled : List U32)
    (item : U32) (h : filled.length=initialized) :
    (filled++[item]).length=initialized+1 := by simp [h]

#print axioms initialized_prefix
#print axioms complete_capture
#print axioms store_before_increment
end R1Z.PV_RDB2F_FromFnGuard
