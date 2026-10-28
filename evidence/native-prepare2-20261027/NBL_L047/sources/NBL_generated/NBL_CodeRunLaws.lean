import S1PreparedCompleteHashErasureV1
set_option autoImplicit false
namespace AspisR1.NBL_CodeRunLaws
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode

def chain {A B : Type} (left : Log×Result A) (k : A → Code B) : Log×Result B :=
  match left.2 with
  | .ok a => let right := run (k a); (left.1++right.1,right.2)
  | .fail e => (left.1,.fail e)
  | .div => (left.1,.div)

/-- Append every chronological attempted call, even when a child fails or
rejects. This uses the existing cohort's typed hash-code interpreter. -/
theorem bind_run {A B : Type} (p : Code A) (k : A → Code B) :
    run (p >>= k)=chain (run p) k := by
  induction p with
  | done a => rfl
  | step r c ih =>
    cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | digest D hash parts c ih =>
    change run (Code.digest D hash parts (fun a => PreparedHashCode.bind (c a) k))=_
    cases call : D.digest hash parts with
    | fail e => simp only [run,call,chain]
    | div => simp only [run,call,chain]
    | ok a =>
      have ha : run (PreparedHashCode.bind (c a) k)=chain (run (c a)) k := ih a
      simp only [run,call]
      rw [ha]
      cases hr : (run (c a)).2 <;> simp only [chain,hr,List.cons_append]

theorem lift_run {A : Type} (r : Result A) : run (monadLift r : Code A)=([],r) := by
  cases r <;> rfl

theorem pure_run {A : Type} (a : A) : run (pure a : Code A)=([],ok a) := rfl

theorem digest_run {H : Type} (D : aspis_core.Digest32 H) (hash : H) (parts : Slice (Slice U8)) :
    run (effects.digest D hash parts)=
      ([Event.digest D hash parts (D.digest hash parts)],D.digest hash parts) := by
  change run (Code.digest D hash parts Code.done)=_
  cases call : D.digest hash parts <;> simp only [run,call]

#print axioms bind_run
#print axioms lift_run
#print axioms pure_run
#print axioms digest_run
end AspisR1.NBL_CodeRunLaws
