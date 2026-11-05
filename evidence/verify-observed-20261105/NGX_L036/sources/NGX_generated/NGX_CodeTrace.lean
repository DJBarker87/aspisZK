import NGX_SemanticRuntime
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NGX_CodeTrace

theorem pure_run {A : Type} (value : A) :
 run (pure value : Code A)=([],ok value) := by rfl

theorem lift_run {A : Type} (reply : Result A) :
 run (monadLift reply : Code A)=([],reply) := by cases reply <;> rfl

theorem lift_bind {A B : Type} (reply : Result A) (next : A→Code B) :
 run ((monadLift reply : Code A)>>=next)=
 (match reply with
  | .ok value => run (next value)
  | .fail error => ([],.fail error)
  | .div => ([],.div)) := by cases reply <;> rfl

theorem digest_bind {A H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (parts : Slice (Slice U8)) (next : Array U8 32#usize→Code A) :
 run (effects.digest D hash parts >>= next)=
 (match D.digest hash parts with
  | .ok value =>
    let tail := run (next value)
    (Event.digest D hash parts (ok value)::tail.1,tail.2)
  | .fail error => ([Event.digest D hash parts (.fail error)],.fail error)
  | .div => ([Event.digest D hash parts .div],.div)) := by
 cases h : D.digest hash parts with
 | ok value =>
   cases tail : run (next value)
   simp only [effects,PreparedHashCode.bind,run,h,tail]
 | fail error => simp only [effects,PreparedHashCode.bind,run,h]
 | div => simp only [effects,PreparedHashCode.bind,run,h]
#print axioms pure_run
#print axioms lift_run
#print axioms lift_bind
#print axioms digest_bind
end AspisR1.NGX_CodeTrace
