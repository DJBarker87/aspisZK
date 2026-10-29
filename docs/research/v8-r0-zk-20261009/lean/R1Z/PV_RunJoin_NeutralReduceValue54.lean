import R1Z.PV_RunJoin_NeutralValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralReduceValue54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_NeutralValue54

theorem complete (x : U64) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 x=ok y ∧
      Canon y ∧ scalar y=(x.val : M) := by
  obtain ⟨y,hy,hv⟩ := PV_RunJoin_CircleNeutralResidue53.reduce_mod x
  refine ⟨y,hy,?_,residue y _ hv⟩
  unfold Canon;rw [hv];exact Nat.mod_lt _ (by decide)
#print axioms complete
end R1Z.PV_RunJoin_NeutralReduceValue54
