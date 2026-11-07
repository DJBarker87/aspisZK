import NMS_GeneralGetters
import NMS_NormalRefine
set_option autoImplicit false
namespace NMS_CloneNormal
open RSL NMS_RSLSuccess

theorem allocate_events (env : Env) (u : Unit) (events : List Event)
 (run : Spec.alloc env ⟨.ret u,events⟩) : events = [] := by
 rcases run with same | same
 · exact congrArg Obs.events same
 · exact congrArg Obs.events same

theorem clone (error : ProgramError) (env : Env) (reply : ProgramError) (events : List Event)
 (run : NMS_CloneReference.clone error env ⟨.ret reply,events⟩) : reply = error ∧ events = [] := by
 cases error <;> simp only [NMS_CloneReference.clone] at run
 all_goals first
 | (exact ⟨pure_return _ _ env events run,congrArg Obs.events run⟩)
 | (split at run
    · exact ⟨pure_return _ _ env events run,congrArg Obs.events run⟩
    · obtain ⟨u,e1,e2,first,last,same⟩ := bind_return _ _ _ _ _ run
      refine ⟨pure_return _ _ _ _ last,?_⟩
      have ending : e2 = [] := congrArg Obs.events last
      rw [same,allocate_events env u e1 first,ending]
      rfl)

theorem getter {A : Type} (stored : Except ProgramError A) (env : Env)
 (reply : Except ProgramError A) (events : List Event)
 (run : NMS_GeneralGetters.get stored env ⟨.ret reply,events⟩) :
 reply = stored ∧ events = [] := by
 cases stored with
 | ok value => exact ⟨pure_return _ _ env events run,congrArg Obs.events run⟩
 | error error =>
   obtain ⟨copied,e1,e2,first,last,same⟩ := bind_return _ _ _ _ _ run
   obtain ⟨unchanged,empty⟩ := clone error env copied e1 first
   have returned := pure_return _ _ _ _ last
   refine ⟨?_,?_⟩
   · exact returned.trans (congrArg Except.error unchanged)
   · have ending : e2 = [] := congrArg Obs.events last
     rw [same,empty,ending]
     rfl

theorem normal {A : Type} (stored : Except ProgramError A) :
 NMS_NormalRefine.Normal (NMS_GeneralGetters.get stored) (RS.ofExcept stored) := by
 intro env reply events run
 obtain ⟨same,empty⟩ := getter stored env reply events run
 cases same
 cases empty
 rfl
#print axioms allocate_events
#print axioms clone
#print axioms getter
#print axioms normal
end NMS_CloneNormal
