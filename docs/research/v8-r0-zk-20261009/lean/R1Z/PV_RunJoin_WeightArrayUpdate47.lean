import R1Z.PV_RunJoin_WeightFactorRestore47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightArrayUpdate47
open Aeneas Aeneas.Std Result

theorem complete {A : Type} {N : Usize} (a : Array A N) (i : Usize)
    (hi : i.val<N.val) (x : A) :
    Array.update a i x=ok (Aeneas.Std.Array.set a i x) := by
  obtain ⟨old,hr,_⟩ := WP.spec_imp_exists (Array.index_usize_spec a i (by
    change i.val<a.val.length
    rw [a.property]
    exact hi))
  have hg := PV_RunJoin_WeightFactorRestore47.read_value a i old hr
  change a[i]?=some old at hg
  unfold Array.update
  rw [hg]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightArrayUpdate47
