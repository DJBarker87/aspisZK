import Aeneas
/-! State-threaded from_fn projection: each FnMut return supplies the captured
state to the next index. Raw MaybeUninit/provenance adequacy remains separate. -/
namespace R1Z.PV_RDB2E_FromFn
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def build {S A : Type} (f : Nat → S → Result (A × S)) : Nat → Nat → S → Result (List A × S)
  | 0,_,s => ok ([],s)
  | n+1,i,s => do
    let (a,s1) ← f i s
    let (tail,s2) ← build f n (i+1) s1
    ok (a::tail,s2)

theorem zero {S A : Type} (f : Nat → S → Result (A × S)) (i : Nat) (s : S) :
    build f 0 i s=ok ([],s) := rfl

theorem step {S A : Type} (f : Nat → S → Result (A × S)) (n i : Nat) (s : S) :
    build f (n+1) i s=
      (do let (a,current) ← f i s
          let (tail,after) ← build f n (i+1) current
          ok (a::tail,after)) := rfl

theorem length {S A : Type} (f : Nat → S → Result (A × S)) (n i : Nat) (s after : S)
    (out : List A) (h : build f n i s=ok (out,after)) : out.length=n := by
  induction n generalizing i s out after with
  | zero =>
    simp only [build,Result.ok.injEq,Prod.mk.injEq] at h
    rw [←h.1]; rfl
  | succ n ih =>
    simp only [build] at h
    cases hf : f i s with
    | fail e => simp [hf] at h
    | div => simp [hf] at h
    | ok result =>
      rcases result with ⟨a,s1⟩
      simp only [hf,bind_tc_ok] at h
      dsimp only at h
      cases hb : build f n (i+1) s1 with
      | fail e => simp [hb] at h
      | div => simp [hb] at h
      | ok result =>
        rcases result with ⟨tail,s2⟩
        simp only [hb,bind_tc_ok] at h
        dsimp only at h
        have e : a::tail=out := congrArg Prod.fst (Result.ok.inj h)
        rw [←e]
        exact congrArg Nat.succ (ih (i+1) s1 tail s2 hb)

#print axioms zero
#print axioms step
#print axioms length
end R1Z.PV_RDB2E_FromFn
