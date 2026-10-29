import R1Z.PV_RunJoin_NeutralValue54
import R1Z.PV_RunJoin_CircleNeutralMulResidue53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralMulValue54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_NeutralValue54

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.mul a b=ok y ∧
      Canon y ∧ scalar y=scalar a*scalar b := by
  obtain ⟨y,hy,_,hv⟩ := PV_RunJoin_CircleNeutralMulResidue53.complete a b ha hb
  refine ⟨y,hy,?_,?_⟩
  · unfold Canon;rw [hv];exact Nat.mod_lt _ (by decide)
  · rw [residue y _ hv,Nat.cast_mul];rfl
#print axioms complete
end R1Z.PV_RunJoin_NeutralMulValue54
