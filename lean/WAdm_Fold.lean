import WAdm_VecStd
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.WAdm_Fold
abbrev Vec := alloc.vec.Vec U8

def body {T : Type} (append : Vec → T → Result Vec) (state : List T × Vec) :
    Result (ControlFlow (List T × Vec) Vec) :=
  match state.1 with
  | [] => ok (done state.2)
  | x::xs => do let out ← append state.2 x; ok (cont (xs,out))

def run {T : Type} (append : Vec → T → Result Vec) (xs : List T) (out : Vec) : Result Vec :=
  loop (body append) (xs,out)

/-- Symbolic finite iteration over the actual remaining list, with each
concrete append's checked bound. No large concrete list is normalized. -/
theorem contents {T : Type} (encode : T → List U8) (width : Nat)
    (length : ∀ x, (encode x).length = width) (append : Vec → T → Result Vec)
    (stepContract : ∀ out x, out.val.length + width ≤ Usize.max →
      ∃ after, append out x = ok after ∧ after.val = out.val ++ encode x)
    (xs : List T) (out : Vec) (bound : out.val.length + width * xs.length ≤ Usize.max) :
    ∃ after, run append xs out = ok after ∧ after.val = out.val ++ xs.flatMap encode := by
  induction xs generalizing out with
  | nil =>
    refine ⟨out,?_,by simp⟩
    unfold run
    rw [loop.eq_def]
    rfl
  | cons x xs ih =>
    have first : out.val.length + width ≤ Usize.max := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at bound
      omega
    obtain ⟨mid,call,midval⟩ := stepContract out x first
    have restBound : mid.val.length + width * xs.length ≤ Usize.max := by
      rw [midval,List.length_append,length]
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at bound
      omega
    obtain ⟨after,tail,afterval⟩ := ih mid restBound
    refine ⟨after,?_,?_⟩
    · unfold run
      rw [loop.eq_def]
      simp only [body,call,bind_tc_ok]
      exact tail
    · rw [afterval,midval,List.flatMap_cons,List.append_assoc]

#print axioms contents
end AspisR1.WAdm_Fold
end
