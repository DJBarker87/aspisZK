import R1Z.PV_RunJoin_MaskFieldTotal69
import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskPreparedTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_RunJoin_MaskFieldTotal69

theorem component (left : Array U32 3#usize) (right : C) :
    ∃ out,host_arithmetic.prepared_component_mul left right=ok out := by
  unfold host_arithmetic.prepared_component_mul
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide)); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
  exact ⟨_,rfl⟩

theorem mul (prepared : host_arithmetic.PreparedQm31Multiplier) (right : Q) :
    ∃ out,host_arithmetic.PreparedQm31Multiplier.mul prepared right=ok out := by
  unfold host_arithmetic.PreparedQm31Multiplier.mul
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide)); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (component _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (hostR _); intro _)
  exact ⟨_,rfl⟩

theorem prepareComponent (a : C) : ∃ out,host_arithmetic.prepare_component a=ok out := by
  unfold host_arithmetic.prepare_component
  obtain ⟨m,hm⟩ := PV_RunJoin_MaskScalarTotal69.add a.a a.b
  exact ⟨_,by simp only [hm,bind_tc_ok]⟩

theorem prepare (a : Q) : ∃ out,host_arithmetic.PreparedQm31Multiplier.new a=ok out := by
  unfold host_arithmetic.PreparedQm31Multiplier.new
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (prepareComponent _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
  exact ⟨_,rfl⟩

theorem power (a : Q) : ∃ out,host_arithmetic.mask_power_26 a=ok out := by
  unfold host_arithmetic.mask_power_26
  repeat' first
    | (apply ProverRwP6BindTotal.bind_total _ _ (qsquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qmul _ _); intro _)
  first | exact qmul _ _ | exact ⟨_,rfl⟩

theorem tower (a : Q) (i : Usize) (bound : i.val<4) :
    ∃ out,host_arithmetic.mul_tower_basis a i=ok out := by
  unfold host_arithmetic.mul_tower_basis
  have cases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases cases with h|h|h|h <;> rw [h]
  all_goals
    repeat' first
      | (apply ProverRwP6BindTotal.bind_total _ _ (hostR _); intro _)
      | (apply ProverRwP6BindTotal.bind_total _ _ (hostI _); intro _)
    exact ⟨_,rfl⟩

#print axioms component
#print axioms mul
#print axioms prepareComponent
#print axioms prepare
#print axioms power
#print axioms tower
end R1Z.PV_RunJoin_MaskPreparedTotal69
