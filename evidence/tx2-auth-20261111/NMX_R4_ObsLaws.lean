import NMX_R4_CallRun
set_option autoImplicit false
noncomputable section
namespace NMX_R4_ObsLaws
open RSL NMX_R2_Observation NMX_R4_CallRun

theorem bind_assoc {A B C : Type} (o : Obs A) (f : A → Obs B) (g : B → Obs C) :
 NMX_R2_Observation.bind (NMX_R2_Observation.bind o f) g = NMX_R2_Observation.bind o (fun a => NMX_R2_Observation.bind (f a) g) := by
 cases o with
 | mk ex es =>
  cases ex with
  | abort => rfl
  | diverge => rfl
  | ret a =>
   cases hf : f a with
   | mk ey fs =>
    cases ey <;> simp only [NMX_R2_Observation.bind,hf,List.append_assoc]

theorem bind_right {A : Type} (o : Obs A) : NMX_R2_Observation.bind o (fun a => ⟨.ret a,[]⟩) = o := by
 cases o with
 | mk ex es => cases ex <;> simp only [NMX_R2_Observation.bind,List.append_nil]

theorem map_bind {A B C : Type} (f : B → C) (o : Obs A) (k : A → Obs B) :
 map f (NMX_R2_Observation.bind o k) = NMX_R2_Observation.bind o (fun a => map f (k a)) := by
 cases o with
 | mk ex es =>
  cases ex with
  | abort => rfl
  | diverge => rfl
  | ret a => cases hk : k a; rfl

theorem bind_congr {A B : Type} (o : Obs A) (f g : A → Obs B) (h : ∀ a, f a = g a) :
 NMX_R2_Observation.bind o f = NMX_R2_Observation.bind o g := congrArg (NMX_R2_Observation.bind o) (funext h)

#print axioms bind_assoc
#print axioms bind_right
#print axioms map_bind
#print axioms bind_congr
end NMX_R4_ObsLaws
end
