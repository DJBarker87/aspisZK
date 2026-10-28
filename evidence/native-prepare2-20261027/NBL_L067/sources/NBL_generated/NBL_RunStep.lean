import NBL_CodeRunLaws
set_option autoImplicit false
namespace AspisR1.NBL_RunStep
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

theorem lift_ok {A B : Type} (r : Result A) (a : A) (k : A → Code B)
    (log : Log) (out : Result B) (call : r=ok a)
    (next : run (k a)=(log,out)) :
    run ((monadLift r : Code A) >>= k)=(log,out) := by
  rw [bind_run,lift_run,call]
  simpa only [chain,List.nil_append] using next

theorem digest_ok {A H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (parts : Slice (Slice U8)) (reply : Array U8 32#usize)
    (k : Array U8 32#usize → Code A) (log : Log) (out : Result A)
    (call : D.digest hash parts=ok reply) (next : run (k reply)=(log,out)) :
    run (effects.digest D hash parts >>= k)=
      (Event.digest D hash parts (ok reply)::log,out) := by
  rw [bind_run,digest_run,call]
  simpa only [chain,next,List.singleton_append] using
    (rfl : (Event.digest D hash parts (ok reply)::log,out)=
      (Event.digest D hash parts (ok reply)::log,out))

#print axioms lift_ok
#print axioms digest_ok
end AspisR1.NBL_RunStep
