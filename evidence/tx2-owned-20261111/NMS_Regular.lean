import NMS_Interpreted
import NMS_RSLSuccess
set_option autoImplicit false
namespace NMS_Regular
open Aeneas Aeneas.Std Result
/-- A returning interpreted execution has the exact emitted value. This
relation permits independent allocation aborts without inventing a reply. -/
def Law {A : Type} (meaning : RSL.Spec A) (code : Result A) : Prop :=
 ∀ env a events, meaning env ⟨.ret a,events⟩ → code = .ok a

theorem lift {A : Type} (code : Result A) : Law (NMS_Interpreted.liftResult code) code := by
 intro env a events run
 cases code with
 | ok value =>
   have same := NMS_RSLSuccess.pure_return value a env events run
   cases same
   rfl
 | fail error => cases run
 | div => cases run

theorem allocate : Law RSL.Spec.alloc (Result.ok ()) := by
 intro env unit events run
 cases unit
 rfl

theorem bind {A B : Type} (meaning : RSL.Spec A) (code : Result A)
 (next : A → RSL.Spec B) (source : A → Result B)
 (first : Law meaning code) (rest : ∀ a, Law (next a) (source a)) :
 Law (RSL.Spec.bind meaning next) (code >>= source) := by
 intro env b events run
 obtain ⟨a,e1,e2,hfirst,hlast,_⟩ := NMS_RSLSuccess.bind_return _ _ _ _ _ run
 rw [first env a e1 hfirst]
 simpa only [bind_tc_ok] using rest a env b e2 hlast
#print axioms lift
#print axioms allocate
#print axioms bind
end NMS_Regular
