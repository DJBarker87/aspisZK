import NMX_Observation
set_option autoImplicit false
namespace NMX_AllocationSound
open RSL NMX_Observation

theorem lift {A : Type} (o : Obs A) (m : Spec A) (env : Env)
 (run : m env o) :
 RS.lift m env (NMX_Observation.bind o (fun a => ⟨.ret (.ok a),[]⟩)) := by
 apply bind_sound o _ m _ env run
 intro a
 rfl

/-- The normal allocation arm and the independent allocator-abort arm are
both admitted at this SAME named site; neither is an arbitrary stop. -/
theorem returned {A : Type} (value : A) (env : Env) :
 RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure value) env ⟨.ret (.ok value),[]⟩ := by
 have first : RS.lift Spec.alloc env ⟨.ret (.ok ()),[]⟩ :=
  lift ⟨.ret (),[]⟩ Spec.alloc env (Or.inl rfl)
 exact rust_sound ⟨.ret (.ok ()),[]⟩ (fun _ => ⟨.ret (.ok value),[]⟩)
  (RS.lift Spec.alloc) (fun _ => RS.pure value) env first (fun _ => rfl)

theorem aborted {A : Type} (value : A) (env : Env) :
 RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure value) env ⟨.abort,[]⟩ := by
 have first : RS.lift Spec.alloc env ⟨.abort,[]⟩ :=
  lift ⟨.abort,[]⟩ Spec.alloc env (Or.inr rfl)
 exact rust_sound ⟨.abort,[]⟩ (fun _ => ⟨.ret (.ok value),[]⟩)
  (RS.lift Spec.alloc) (fun _ => RS.pure value) env first (fun _ => rfl)
#print axioms lift
#print axioms returned
#print axioms aborted
end NMX_AllocationSound
