import LIBB_ModelGraph
set_option autoImplicit false
namespace LIBB_ObservationMap
open Aeneas Aeneas.Std
open RSL NMS_R2N_Interpreted
/-- Carrier conversion is a separate equality, not a native Cut-image law. -/
theorem exact_map {A B : Type} (f : A → B) (m : Spec A) (env : Env) (o : Obs B) :
 Spec.map f m env o ↔ ∃ raw, m env raw ∧ o = mapObs f raw := by
 constructor
 · intro run
   rcases run with ⟨a,e1,o2,hm,hk,ho⟩ | ⟨e1,hm,ho⟩ | ⟨e1,hm,ho⟩
   · change o2 = ⟨.ret (f a),[]⟩ at hk
     subst o2
     exact ⟨⟨.ret a,e1⟩,hm,by simpa only [List.append_nil] using ho⟩
   · exact ⟨⟨.abort,e1⟩,hm,ho⟩
   · exact ⟨⟨.diverge,e1⟩,hm,ho⟩
 · rintro ⟨raw,h,rfl⟩
   exact LIBB_ModelGraph.mapped_member f m env raw h

theorem lift_graph {A B : Type} (f : A → B) (code : Result A) (env : Env) (o : Obs B) :
 Spec.map f (liftResult code) env o ↔ o = LIB_Carriers.resultObs f [] code := by
 rw [exact_map]
 cases code with
 | ok a => simp only [liftResult,Spec.pure,exists_eq_left,mapObs,mapExit,LIB_Carriers.resultObs]
 | fail e => simp only [liftResult,Spec.panic,exists_eq_left,mapObs,mapExit,LIB_Carriers.resultObs]
 | div => simp only [liftResult,exists_eq_left,mapObs,mapExit,LIB_Carriers.resultObs]

theorem alloc_map {A B : Type} (f : A → B) (m : Spec A) (env : Env) (o : Obs B) :
 Spec.map f (Spec.bind Spec.alloc (fun _ => m)) env o ↔
 Spec.map f m env o ∨ o = ⟨.abort,[]⟩ := by
 constructor
 · intro run
   obtain ⟨raw,hr,ho⟩ := (exact_map _ _ _ _).mp run
   rcases (Spec.bind_two _ _ env () (fun _ => Iff.rfl) raw).mp hr with h | h
   · exact Or.inl ((exact_map _ _ _ _).mpr ⟨raw,h,ho⟩)
   · subst raw
     exact Or.inr ho
 · rintro (run | rfl)
   · obtain ⟨raw,hr,ho⟩ := (exact_map _ _ _ _).mp run
     exact (exact_map _ _ _ _).mpr ⟨raw,
       (Spec.bind_two _ _ env () (fun _ => Iff.rfl) raw).mpr (Or.inl hr),ho⟩
   · exact (exact_map _ _ _ _).mpr ⟨⟨.abort,[]⟩,
       (Spec.bind_two _ _ env () (fun _ => Iff.rfl) _).mpr (Or.inr rfl),rfl⟩

theorem two_alloc_graph {A B : Type} (f : A → B) (code : Result A) (env : Env) (o : Obs B) :
 Spec.map f (Spec.bind Spec.alloc (fun _ => Spec.bind Spec.alloc (fun _ => liftResult code))) env o ↔
 o = LIB_Carriers.resultObs f [] code ∨ o = ⟨.abort,[]⟩ := by
 rw [alloc_map,alloc_map,lift_graph]
 simp only [or_assoc,or_self]

/-- A mapped successful return still names the SAME original source event
prefix and value. No source-success premise is introduced. -/
theorem return_source {A B : Type} (f : A → B) (m : Spec A) (env : Env) (b : B) (events : List Event)
 (run : Spec.map f m env ⟨.ret b,events⟩) : ∃ a, m env ⟨.ret a,events⟩ ∧ b = f a := by
 obtain ⟨raw,h,eq⟩ := (exact_map _ _ _ _).mp run
 cases raw with
 | mk exit es =>
   cases exit with
   | abort => cases congrArg Obs.exit eq
   | diverge => cases congrArg Obs.exit eq
   | ret a =>
     have hb : b = f a := Exit.ret.inj (congrArg Obs.exit eq)
     have he : events = es := congrArg Obs.events eq
     exact ⟨a,he.symm ▸ h,hb⟩
#print axioms exact_map
#print axioms lift_graph
#print axioms alloc_map
#print axioms two_alloc_graph
#print axioms return_source
end LIBB_ObservationMap
