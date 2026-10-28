import NDO_JHl_AccumulateSums
import NDO_JHk_RhsFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_SumField
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (Sum)
open AspisV8R15.ExactTowerBase
abbrev K := QM31Exact

def value (s : Sum) (j : Nat) : K :=
  ⟨⟨s j 0,s j 1⟩,⟨s j 2,s j 3⟩⟩

def scalar (x : M31Exact) : K := ⟨⟨x,0⟩,0⟩

theorem step (s u : Sum) (j : Fin 64) (power : aspis_core.field.QM31)
    (basis : Array U32 256#usize)
    (h : ∀ i k,u i k=if i<64 then s i k+
      (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK power) k).val*
        (S7JoinBasisBlock.cell basis i).val else s i k) :
    value u j.val=value s j.val+CheckpointBytes5Output.ofK power*
      scalar (S7JoinBasisMachine.decode (S7JoinBasisBlock.cell basis j.val)) := by
  have decoded : CheckpointBytes5Output.ofK power=
      (⟨⟨(power.c0.a.val : M31Exact),(power.c0.b.val : M31Exact)⟩,
        ⟨(power.c1.a.val : M31Exact),(power.c1.b.val : M31Exact)⟩⟩ : K) := by rfl
  rw [decoded]
  simp only [value,h,if_pos j.isLt,Nat.cast_add,Nat.cast_mul]
  ext <;> simp [scalar,CheckpointBytes5Output.ofK,S7JoinBasisMachine.decode,
    S7Kani2OwnedRowRefinement.powerLimb,Port3_RowsInstall.toK]
#print axioms step
end AspisR1.JHl_SumField
end
