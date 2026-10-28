import NDO_JFu_TransitionFirst
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionShift
open Aeneas Aeneas.Std Result WP

theorem shift2 : (13#u64 >>> 2#usize : Result U64)=ok 3#u64 := by
  have spec : (13#u64 >>> 2#usize : Result U64) ⦃ out => out.val=3 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=3#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call

#print axioms shift2
end AspisR1.JFu_TransitionShift
end
