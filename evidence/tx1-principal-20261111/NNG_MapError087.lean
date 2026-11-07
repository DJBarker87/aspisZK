import NNG_InterpretProjection
import RSL_Verifier
import LIBC_SpecMap
set_option autoImplicit false
namespace AspisR1.NNG_MapError087
open Aeneas Aeneas.Std NMT_CallTree NNG_Observed136

def mapError {E F A : Type} (f : E → F) : Except E A → Except F A
 | .ok a=>.ok a | .error e=>.error (f e)

theorem law {E F A B : Type} (f : E → F) (decode : A → Except E B)
 (events : Event → List RSL.Event) (code : Code A) (env : RSL.Env) (m : RSL.RE E B)
 (head : m env (observation decode events code)) :
 RSL.RE.mapErr f m env (observation (fun a=>mapError f (decode a)) events code) := by
 apply (LIBC_SpecMap.exact (RSL.RE.mapE f) m env _).mpr
 refine ⟨observation decode events code,head,?_⟩
 unfold observation LIBC_SpecMap.observation
 generalize run code = out
 rcases out with ⟨r,log⟩
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok a=>cases decode a <;> rfl
#print axioms law
end AspisR1.NNG_MapError087
