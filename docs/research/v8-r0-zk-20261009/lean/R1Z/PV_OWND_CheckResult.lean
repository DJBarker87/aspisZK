import R1Z.PV_OWND_InitialCheck
set_option autoImplicit false
namespace R1Z.PV_OWND_CheckResult
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWND_InitialCheck

theorem success {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (error : CheckError → E) (b : Buffer Link) (w : State S X) (h:checks b=.ok ()) :
 finish dealloc error b w=⟨.ok b,w,[]⟩ := by simp only [finish,h,lift]

theorem error_cleanup {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (error : CheckError → E) (b : Buffer Link) (w : State S X) (e : CheckError)
 (h:checks b=.error e) :
 finish dealloc error b w=
 bind (dropOwned b.owner (fun _=>dropVecPod dealloc b.token b.cell))
  (fun _=>lift (.fail (error e))) w := by simp only [finish,h]
#print axioms success
#print axioms error_cleanup
end R1Z.PV_OWND_CheckResult
