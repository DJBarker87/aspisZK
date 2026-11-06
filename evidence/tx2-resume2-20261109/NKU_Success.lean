import NKU_Chronology
set_option autoImplicit false
namespace NKU_Success
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def Ensures {A : Type} (m : Run (core.result.Result A verifier.Error)) (p : A → Prop) : Prop :=
 ∀ a,m.result=ok (.Ok a) → p a
theorem bind {A B : Type} (m : Run A) (next : A → Run (core.result.Result B verifier.Error))
 (p : B → Prop) (tail : ∀ a,Ensures (next a) p) : Ensures (m >>= next) p := by
 intro b returned
 rw [NJU_Log.erase_bind] at returned
 cases h : m.result with
 | fail err => rw [h] at returned;cases returned
 | div => rw [h] at returned;cases returned
 | ok a => rw [h] at returned;exact tail a b returned
theorem pure {A : Type} (p : A → Prop) (a : A) (h : p a) : Ensures (pure (.Ok a)) p := by
 intro b returned
 cases returned
 exact h
theorem reject {A : Type} (p : A → Prop) (err : verifier.Error) : Ensures (Pure.pure (.Err err)) p := by
 intro a returned
 cases returned
#print axioms bind
#print axioms pure
#print axioms reject
end NKU_Success
