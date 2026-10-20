import R1Z.CausalPremisesR1PBin

/-! A counterexample admitted by the current wire interface. The row-zero
frame may read the C2 root, although the protocol constructs C2 after row 1.
An order fact cannot repair such an encoding on counterfactual vectors. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.CausalOrderObstructionBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.PremisesR1PBin
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- A legal wire encoding under today's structure: every semantic row
includes the supplied C2 digest. This is not the protocol encoding. -/
def prematureC2 (W : R1Wire K CommitHandle Aux) : R1Wire K CommitHandle Aux :=
  { W with frame := fun _ root _ => ans root }

/-- Universal RCausal fails for this legal wire whenever C2 is not before
row zero. Neither successful-run restrictions nor hash collision assumptions
are involved. -/
theorem prematureC2_not_causal (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F (prematureC2 W))
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (late : ¬ Pr.ord.symm (.inr (.inl 1)) < Pr.ord.symm (.inl (.absS 0))) :
    ¬ RCausal (prematureC2 W) Pr h B outputs x w := by
  intro hc
  let v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer := fun _ => 0
  let v' : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer :=
    Function.update v (.inr (.inl 1)) (fun _ => 1)
  have he : Earlier (prematureC2 W) Pr (.inl (.absS 0)) v v' := by
    intro q hq
    have hn : q ≠ .inr (.inl 1) := by
      intro eq
      subst q
      exact late hq
    exact (Function.update_of_ne hn _ _).symm
  have eq := (causal_iff (prematureC2 W) Pr h B outputs x w).mp hc
    (fun _ => Classical.choice (inferInstance : Nonempty NZ)) 0 (.inl (.absS 0)) v v' he
  have bytes : ans (0 : OracleAnswer) = ans (fun _ => (1 : UInt8)) := by
    simpa [attAddr, addr, addrWith, fieldVal, fc, recP, prematureC2,
      rootsOf, trOf, v', v] using eq
  have first := congrArg (fun bs : List UInt8 => bs.getD 0 0) bytes
  have bad : (0 : UInt8) = 1 := by
    simpa [ans, List.getD_eq_getElem?_getD] using first
  exact (by decide : (0 : UInt8) ≠ 1) bad

#print axioms prematureC2_not_causal
end R1Z.CausalOrderObstructionBin
