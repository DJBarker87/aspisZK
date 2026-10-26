import Port4C_InverseExecution
import SAQ_InverseFieldModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Inverse
open Aeneas Aeneas.Std Result

def source (x : U32) : Result U32 :=
  AspisR1M31Inverse.field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x

theorem canonical_injective (x y : U32) (hx : x.val<AspisCircleGroupOrder.P)
    (hy : y.val<AspisCircleGroupOrder.P)
    (same : S7JoinBasisMachine.decode x=S7JoinBasisMachine.decode y) : x=y := by
  have values := congrArg ZMod.val same
  change x.val % AspisCircleGroupOrder.P=y.val % AspisCircleGroupOrder.P at values
  rw [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at values
  exact UScalar.eq_of_val_eq values

/-- Full Result equality at every raw U32, including zero and noncanonical
nonzero representations of field zero. No nonzero-field premise is added. -/
theorem source_eq_reference : source=Port4C_InverseExecution.inverse_owned := by
  funext x
  by_cases hx : x=0#u32
  · subst x
    simp only [source,AspisR1M31Inverse.field.M31.inv,
      Port4C_InverseExecution.inverse_result,bne_self,massert,reduceCtorEq,if_false,bind_tc_fail]
  · have hxBool : x != 0#u32 := by simpa only [bne_iff_ne] using hx
    obtain ⟨out,run,value⟩ := AspisR1M31Inverse.SquareProof.current_inv_total_power x hxBool
    have canonical := AspisR1M31Inverse.SquareProof.current_inv_success_canonical x out run
    have same : out=Port4C_InverseBackend.inverseWord x := by
      apply canonical_injective out _ canonical (Port4C_InverseExecution.inverse_canonical x)
      change R17CurrentM31Semantics.decode out = _
      rw [value,Port4C_InverseBackend.chain_exponent]
      rfl
    change AspisR1M31Inverse.field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = _
    rw [run,same,Port4C_InverseExecution.inverse_result]
    simp only [hx,massert,if_true,bind_tc_ok]

#print axioms canonical_injective
#print axioms source_eq_reference
end AspisR1.SAQ_Inverse
end
