import ArrayFromFnCopyStable
import AspisR1.PoseidonFullRoundCellStep

/-! Reuse the proved source Copy constructor with four stable scalar
callbacks, retaining an arbitrary property of each actual output limb. -/
set_option autoImplicit false
namespace AspisR1.PoseidonRaw4Constructor
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (cell)

theorem source_success {C : Type} (inst : core.ops.function.FnMut C Usize U64)
    (c : C) (R : Fin 4 → U64 → Prop)
    (hcall : ∀ (i : Usize) (hi : i.val < 4), ∃ v : U64,
      inst.call_mut c i = .ok (v,c) ∧ R ⟨i.val,hi⟩ v) :
    ∃ out : Array U64 4#usize,
      array_from_fn_copy 4#usize core.marker.CopyU64 inst 0#u64 c = .ok out ∧
      ∀ j : Fin 4, R j (cell out j) := by
  classical
  have hc : ∀ j : Fin 4, ∃ v : U64,
      inst.call_mut c (UScalar.ofNatCore j.val (by scalar_tac)) = .ok (v,c) ∧ R j v := by
    intro j
    let idx : Usize := UScalar.ofNatCore j.val (by scalar_tac)
    have hidx : idx.val = j.val := by scalar_tac
    have hb : idx.val < 4 := by rw [hidx]; exact j.isLt
    obtain ⟨v,hv,hr⟩ := hcall idx hb
    have hfin : (⟨idx.val,hb⟩ : Fin 4) = j := Fin.ext hidx
    rw [hfin] at hr
    exact ⟨v,hv,hr⟩
  choose values hvalues hprops using hc
  let value : Nat → U64 := fun n => if h : n < 4 then values ⟨n,h⟩ else 0#u64
  have hstable : ∀ i : Usize, i.val < (4#usize).val →
      inst.call_mut c i = .ok (value i.val,c) := by
    intro i hi
    have hb : i.val < 4 := by simpa using hi
    let j : Fin 4 := ⟨i.val,hb⟩
    have hj := hvalues j
    have hidx : (UScalar.ofNatCore j.val (by scalar_tac) : Usize) = i := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    rw [hidx] at hj
    simpa only [value,dif_pos hb] using hj
  obtain ⟨out,hrun,hout⟩ := array_from_fn_copy_stable 4#usize core.marker.CopyU64 inst
    0#u64 c value hstable
  refine ⟨out,hrun,?_⟩
  intro j
  have hb : j.val < (4#usize).val := by simpa using j.isLt
  have hj := hout j.val hb
  have hcell : cell out j = values j := by
    simpa only [cell,value,dif_pos j.isLt] using hj
  rw [hcell]
  exact hprops j

#print axioms source_success
end AspisR1.PoseidonRaw4Constructor
