import NNG_TryObservation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BindAssociation345
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136

theorem source {A B C D : Type} (f : A → B) (g : C → D)
 (events : Event → List RSL.Event) (head : Code A) (next : A → Code C)
 (tail : B → RSL.Obs D)
 (later : ∀ a, observation g events (next a)=tail (f a)) :
 observation g events (NMT_CallTree.bind head next)=
 NNG_Obs345.bindObs (observation f events head) tail := by
 rw [NNG_ObservationAlgebra.observation_bind]
 unfold NNG_ObservationAlgebra.append NNG_Obs345.bindObs observation
 generalize run head=out
 rcases out with ⟨r,es⟩
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok a=>
  change RSL.Obs.mk (observation g events (next a)).exit
    (es.flatMap events ++ (observation g events (next a)).events)=_
  rw [later a]
  rfl
#print axioms source
end AspisR1.NNG_BindAssociation345
