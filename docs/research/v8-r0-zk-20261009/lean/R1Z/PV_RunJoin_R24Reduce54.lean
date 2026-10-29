import R1Z.PV_RunJoin_CircleNeutralR24Word53
import R1Z.PV_RunJoin_CircleNeutralReduceCompare53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Reduce54
open PV_RunJoin_CircleNeutralR24Word53 PV_RunJoin_CircleNeutralShape53

theorem complete (n : Nat) (hn : n<18446744073709551616) :
    ∃ y, PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 (word n)=ok y ∧
      Canon y ∧ y.val=n%2147483647 := by
  obtain ⟨y,hy,hres⟩ := PV_RunJoin_CircleNeutralResidue53.reduce_mod (word n)
  refine ⟨y,?_,?_,?_⟩
  · unfold PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64
    rw [PV_RunJoin_CircleNeutralReduceCompare53.complete (word n),hy,bind_tc_ok]
  · unfold Canon
    rw [hres]
    exact Nat.mod_lt _ (by decide)
  · rw [hres,value n hn]
#print axioms complete
end R1Z.PV_RunJoin_R24Reduce54
