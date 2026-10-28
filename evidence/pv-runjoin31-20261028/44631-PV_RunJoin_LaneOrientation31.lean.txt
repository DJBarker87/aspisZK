import R1Z.PV_RunJoin_LaneDenotation31
import R1Z.PV_RunJoin_LaneCounts31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LaneOrientation31
open Aeneas Aeneas.Std Result
open PV_RunJoin_LaneFold31

theorem reverse_original (input : PV_RunJoin_LaneDenotation31.Pair) (level : Fin 20) :
    PV_RunJoin_LaneDenotation31.reverse input level.val =
      !((U32.wrapping_shr input.membership.index
        (UScalar.cast .U32 (Usize.ofNatCore level.val (by have := level.isLt; scalar_tac))) &&& 1#u32) == 0#u32) := by
  unfold PV_RunJoin_LaneDenotation31.reverse
  rw [Nat.mod_eq_of_lt level.isLt,PV_RunJoin_LaneCounts31.shift]
  rfl
#print axioms reverse_original

theorem step_original (parent : Digest → Digest → Result Digest)
    (input : PV_RunJoin_LaneDenotation31.Pair) (current : Digest) (level : Fin 20) :
    step parent current (PV_RunJoin_LaneDenotation31.sibling input level.val)
      (PV_RunJoin_LaneDenotation31.reverse input level.val) =
      (if ((U32.wrapping_shr input.membership.index
        (UScalar.cast .U32 (Usize.ofNatCore level.val (by have := level.isLt; scalar_tac))) &&& 1#u32) == 0#u32)
       then parent current (PV_RunJoin_LaneDenotation31.sibling input level.val)
       else parent (PV_RunJoin_LaneDenotation31.sibling input level.val) current) := by
  rw [reverse_original]
  exact PV_RunJoin_LaneFold31.step_original _ _ _ _
#print axioms step_original
end R1Z.PV_RunJoin_LaneOrientation31
