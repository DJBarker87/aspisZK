import RPv_JFy_Steps
import RPv_FIy_MapValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDE_Map
open Aeneas Aeneas.Std Result WP

theorem loop {T C A : Type} (f : C → A → Result (T × C)) (P : T → Prop)
    (xs : List A) (c : C) (step : ∀ x∈xs,∃ y,f c x=ok (y,c) ∧ P y) :
    ∃ ys,AspisV8R19.TraversalRuntime.mapState f xs c=ok (ys,c) ∧ ys.length=xs.length ∧ ∀ y∈ys,P y := by
  induction xs with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨y,hy,hyp⟩ := step x (by simp)
    obtain ⟨ys,hys,hlen,hp⟩ := ih (by intro a ha;exact step a (by simp [ha]))
    refine ⟨y::ys,?_,by simp [hlen],?_⟩
    · simp only [AspisV8R19.TraversalRuntime.mapState,hy,bind_tc_ok,hys]
    · intro z hz
      rcases List.mem_cons.mp hz with rfl|hz
      · exact hyp
      · exact hp z hz
#print axioms loop

theorem source {T C A : Type} {N : Usize} (f : core.ops.function.FnMut C A T)
    (P : T → Prop) (a : Array A N) (c : C)
    (step : ∀ x∈a.val,∃ y,f.call_mut c x=ok (y,c) ∧ P y) :
    ∃ out,core.array.Array.map f a c=ok out ∧ ∀ y∈out.val,P y := by
  obtain ⟨ys,hys,hlen,hp⟩ := loop f.call_mut P a.val c step
  have size : ys.length=N.val := hlen.trans a.property
  refine ⟨⟨ys,size⟩,?_,hp⟩
  unfold core.array.Array.map
  split
  · rename_i zs last called
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj (hys.symm.trans called))
    rfl
  · rename_i e failed
    rw [hys] at failed
    cases failed
  · rename_i diverged
    rw [hys] at diverged
    cases diverged

#print axioms source
end AspisR1.NDE_Map
end
