import NCJ_ScalarFoldStep
import NCJ_Constants
set_option autoImplicit false
noncomputable section
namespace NCJ_ScalarFactorTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues NCJ_ScalarFoldStep

theorem fold (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (hp : ∀ x∈p.val,canonE x) (v : NE) (hv : canonE v) (iter : Iter)
    (end4 : iter.end.val=4) (bound : iter.start.val≤4) :
    ∃ out,FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop iterator fnmut
      iter (p,f) v=ok out ∧ canonE out := by
  let inv : (Iter × Closure × NE) → Prop := fun s=>s.1.end.val=4 ∧ s.1.start.val≤4 ∧
    s.2.1=(p,f) ∧ canonE s.2.2
  have spec : WP.spec (FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop iterator fnmut
      iter (p,f) v) canonE := by
    unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop
    apply loop.spec_decr_nat (fun s : Iter × Closure × NE=>4-s.1.start.val) inv canonE
      (fun s=>body s.1 s.2.1 s.2.2) (iter,(p,f),v)
    · rintro ⟨cursor,closure,value⟩ ⟨he,hb,hc,hv⟩
      change cursor.end.val=4 at he
      change cursor.start.val≤4 at hb
      change closure=(p,f) at hc
      change canonE value at hv
      dsimp! only
      by_cases more : cursor.start.val< cursor.end.val
      · obtain ⟨rest,out,run,inc,end4,co⟩ := NCJ_ScalarFoldStep.active p f hp value hv cursor he more
        have original := (congrArg (fun c : Closure=>body cursor c value) hc).trans run
        unfold body at original
        unfold WP.spec
        rw [original]
        change (rest.end.val=4 ∧ rest.start.val≤4 ∧ (p,f)=(p,f) ∧ canonE out) ∧
          4-rest.start.val<4-cursor.start.val
        exact ⟨⟨end4,by omega,rfl,co⟩,by omega⟩
      · with_unfolding_all rw [NCJ_ScalarFoldStep.done cursor value closure (by omega),WP.spec_ok]
        exact hv
    · exact ⟨end4,bound,rfl,hv⟩
  exact WP.spec_imp_exists spec

theorem source (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (hp : ∀ x∈p.val,canonE x) :
    ∃ out,FIo_Native.weights.Weights.scalar_factor f p=ok out ∧ canonE out := by
  obtain ⟨sum,run,cs⟩ := fold p f hp FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
    NCJ_Constants.zero {start:=0#usize,«end»:=4#usize} rfl (by decide)
  obtain ⟨out,scaled,co,_⟩ := NBG_FieldDischarge.wide_scale sum FIo_Native.weights.QUARTER
  refine ⟨out,?_,co⟩
  simp only [FIo_Native.weights.Weights.scalar_factor,
    FIo_Native.core.iter.traits.iterator.Iterator.fold.default,run,scaled,bind_tc_ok]

#print axioms fold
#print axioms source
end NCJ_ScalarFactorTotal
