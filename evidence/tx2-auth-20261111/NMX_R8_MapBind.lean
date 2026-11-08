import LIBB_ObservationMap
import NMX_R8_SimulatesPath
set_option autoImplicit false
namespace NMX_R8_MapBind
open RSL NMS_R2N_Interpreted

theorem map_bind {A B C : Type} (f : A → B) (m : Spec A) (k : B → Spec C) :
 Spec.bind (Spec.map f m) k = Spec.bind m (fun a => k (f a)) := by
 funext env o
 apply propext
 constructor
 · intro run
   rcases run with ⟨b,events,next,first,last,same⟩ | ⟨events,first,same⟩ | ⟨events,first,same⟩
   · obtain ⟨a,source,eq⟩ := LIBB_ObservationMap.return_source f m env b events first
     subst b
     exact Or.inl ⟨a,events,next,source,last,same⟩
   · obtain ⟨raw,source,eq⟩ := (LIBB_ObservationMap.exact_map f m env _).mp first
     cases raw with
     | mk exit es =>
       cases exit with
       | ret a => cases congrArg Obs.exit eq
       | diverge => cases congrArg Obs.exit eq
       | abort =>
         have ev : events = es := congrArg Obs.events eq
         subst es
         exact Or.inr (Or.inl ⟨events,source,same⟩)
   · obtain ⟨raw,source,eq⟩ := (LIBB_ObservationMap.exact_map f m env _).mp first
     cases raw with
     | mk exit es =>
       cases exit with
       | ret a => cases congrArg Obs.exit eq
       | abort => cases congrArg Obs.exit eq
       | diverge =>
         have ev : events = es := congrArg Obs.events eq
         subst es
         exact Or.inr (Or.inr ⟨events,source,same⟩)
 · intro run
   rcases run with ⟨a,events,next,first,last,same⟩ | ⟨events,first,same⟩ | ⟨events,first,same⟩
   · exact Or.inl ⟨f a,events,next,LIBB_ModelGraph.mapped_member f m env _ first,last,same⟩
   · exact Or.inr (Or.inl ⟨events,LIBB_ModelGraph.mapped_member f m env _ first,same⟩)
   · exact Or.inr (Or.inr ⟨events,LIBB_ModelGraph.mapped_member f m env _ first,same⟩)

theorem lift_bind {A B : Type} (m : Spec A) (k : A → RS B) :
 RS.bind (RS.lift m) k = Spec.bind m k := by
 unfold RS.bind RS.lift
 rw [map_bind]
#print axioms map_bind
#print axioms lift_bind
end NMX_R8_MapBind
