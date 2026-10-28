import R1Z.PV_RDB2C_PV_B2_C_PowersTotal
set_option autoImplicit false
namespace PV_B2_C_Powers7Total
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_PowersBody

def Total {α : Type} (r : Result α) : Prop := ∃ x, r = ok x

theorem bind_total {α β : Type} (r : Result α) (k : α → Result β)
    (hr : Total r) (hk : ∀ x, Total (k x)) : Total (r >>= k) := by
  obtain ⟨x,hx⟩ := hr
  obtain ⟨y,hy⟩ := hk x
  exact ⟨y,by rw [hx,bind_tc_ok,hy]⟩

theorem read7 (a : Array E 7#usize) (i : Usize) (hi : i.val < 7) :
    Total (Array.index_usize a i) := by
  obtain ⟨x,hx,_⟩ := WP.spec_imp_exists (Array.index_usize_spec a i (by
    change i.val < a.val.length
    rw [a.property]
    exact hi))
  exact ⟨x,hx⟩

theorem source (x : E) : Total (host_weights.powers7 x) := by
  unfold host_weights.powers7
  apply bind_total _ _ (PV_B2_C_PowersTotal.source 7#usize x)
  intro a
  apply bind_total _ _ (read7 a 0#usize (by decide))
  intro x0
  apply bind_total _ _ (read7 a 1#usize (by decide))
  intro x1
  apply bind_total _ _ (read7 a 2#usize (by decide))
  intro x2
  apply bind_total _ _ (read7 a 3#usize (by decide))
  intro x3
  apply bind_total _ _ (read7 a 4#usize (by decide))
  intro x4
  apply bind_total _ _ (read7 a 5#usize (by decide))
  intro x5
  apply bind_total _ _ (read7 a 6#usize (by decide))
  intro x6
  exact ⟨_,rfl⟩
#print axioms Total
#print axioms bind_total
#print axioms read7
#print axioms source
end PV_B2_C_Powers7Total
