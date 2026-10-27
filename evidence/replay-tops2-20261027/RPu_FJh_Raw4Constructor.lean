import RPu_FJh_Base
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_Raw4Constructor
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (cell)
theorem source_success {C : Type} (inst : core.ops.function.FnMut C Usize U64)
    (c : C) (R : Fin 4 → U64 → Prop)
    (hcall : ∀ (i : Usize) (hi : i.val < 4), ∃ v : U64,
      inst.call_mut c i = .ok (v,c) ∧ R ⟨i.val,hi⟩ v) :
    ∃ out : Array U64 4#usize,
      array_from_fn_copy 4#usize core.marker.CopyU64 inst 0#u64 c = .ok out ∧
      ∀ j : Fin 4, R j (cell out j) := by
  obtain ⟨out,run⟩ := FJb_BuilderTotal.value 4#usize core.marker.CopyU64 inst 0#u64 c
    (by intro i hi;obtain ⟨v,hv,_⟩:=hcall i hi;exact ⟨v,hv⟩)
  refine ⟨out,run,?_⟩
  intro j
  let i : Usize := Usize.ofNatCore j.val (by scalar_tac)
  have hi : i.val<4 := j.isLt
  have hc := FJb_BuilderSelected.value 4#usize core.marker.CopyU64 inst 0#u64 c
    (by intro k hk;obtain ⟨v,hv,_⟩:=hcall k hk;exact ⟨v,hv⟩) out run i hi
  obtain ⟨v,hv,hr⟩ := hcall i hi
  have eq : v=cell out j := congrArg Prod.fst (Result.ok.inj (hv.symm.trans hc))
  have hj : (⟨i.val,hi⟩ : Fin 4)=j := Fin.ext rfl
  rw [hj,eq] at hr
  exact hr
#print axioms source_success
end AspisR1.FJh_Raw4Constructor
end
