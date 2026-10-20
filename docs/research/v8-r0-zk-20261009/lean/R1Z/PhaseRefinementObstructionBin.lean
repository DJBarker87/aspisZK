import R1Z.PhaseLocalityBin
import R1Z.CausalOrderObstructionBin

/-! The phase wrapper is a substantive refinement, not a way of wrapping any
old wire. The existing D85 witness cannot satisfy even its root-use field. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseRefinementObstructionBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.GamesR1PBin
  R1Z.LensR1 R1Z.PhaseLocalityBin R1Z.CausalOrderObstructionBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem prematureC2_excluded (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (wire : R1Wire K CommitHandle Aux) (W : R1PhaseWire h B outputs x)
    (hw : W.toWire = prematureC2 wire) : False := by
  have he := W.frame_local w tape0 (fun _ => 0) (fun _ => 0)
    (0 : OracleAnswer) (fun _ => (1 : UInt8)) 0
    (fun _ _ _ => rfl) (by intro hi; contradiction)
  have bytes : ans (0 : OracleAnswer) = ans (fun _ => (1 : UInt8)) := by
    simpa only [hw, prematureC2] using he
  have first := congrArg (fun bs : List UInt8 => bs.getD 0 0) bytes
  have bad : (0 : UInt8) = 1 := by
    simpa [ans, List.getD_eq_getElem?_getD] using first
  exact (by decide : (0 : UInt8) ≠ 1) bad

#print axioms prematureC2_excluded
end R1Z.PhaseRefinementObstructionBin
