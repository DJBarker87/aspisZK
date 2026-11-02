import PV_B3_AuditSourceD324
import R1Z.PV_RunJoin_MaskPreparedTotal69
import R1Z.PV_RunJoin_WeightArrayUpdate47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyChannelsTotal72
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_RunJoin_MaskFieldTotal69
attribute [local irreducible] host_arithmetic.accumulate_channels
  host_arithmetic.reconstruct_component host_arithmetic.reconstruct_channels
  aspis_core.field.M31.add aspis_core.field.M31.sub aspis_core.field.M31.reduce_u64
  aspis_core.field.CM31.add aspis_core.field.CM31.sub host_arithmetic.cm31_mul_r
  Array.index_usize Array.index_mut_usize Array.update

theorem borrow {T : Type} {n : Usize} (a : Array T n) (i : Usize) (hi : i.val<n.val) :
    ∃ out,Array.index_mut_usize a i=ok out := by
  obtain ⟨x,hx⟩ := ProverRwP6ArrayRead.read a i hi
  exact ⟨(x,Aeneas.Std.Array.set a i),by simp only [Array.index_mut_usize,hx,bind_tc_ok]⟩

theorem store {T : Type} {n : Usize} (a : Array T n) (i : Usize) (hi : i.val<n.val) (x : T) :
    ∃ out,Array.update a i x=ok out :=
  ⟨Aeneas.Std.Array.set a i x,PV_RunJoin_WeightArrayUpdate47.complete a i hi x⟩

theorem accumulate (sums : Array (Array U64 3#usize) 3#usize) (left right : Q) :
    ∃ out,host_arithmetic.accumulate_channels sums left right=ok out := by
  unfold host_arithmetic.accumulate_channels
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry]
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide));intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (borrow _ _ (by decide));intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (store _ _ (by decide) _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
  exact ⟨_,rfl⟩

theorem component (channels : Array U64 3#usize) :
    ∃ out,host_arithmetic.reconstruct_component channels=ok out := by
  unfold host_arithmetic.reconstruct_component
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry]
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide));intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
  exact ⟨_,rfl⟩

theorem reconstruct (sums : Array (Array U64 3#usize) 3#usize) :
    ∃ out,host_arithmetic.reconstruct_channels sums=ok out := by
  unfold host_arithmetic.reconstruct_channels
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry]
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide));intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (component _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (hostR _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
  exact ⟨_,rfl⟩

theorem complete (left right : Array Q 3#usize) :
    ∃ out,host_arithmetic.qm31_sum_products3 left right=ok out := by
  unfold host_arithmetic.qm31_sum_products3
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry]
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide));intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
    | (apply ProverRwP6BindTotal.bind_total _ _ (accumulate _ _ _);intro _;simp only [lift,bind_tc_ok,Aeneas.Std.uncurry])
  exact reconstruct _

#print axioms borrow
#print axioms store
#print axioms accumulate
#print axioms component
#print axioms reconstruct
#print axioms complete
end R1Z.PV_RunJoin_PolyChannelsTotal72
