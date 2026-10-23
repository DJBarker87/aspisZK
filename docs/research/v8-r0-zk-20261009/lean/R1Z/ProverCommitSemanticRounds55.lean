import R1Z.ProverCommitSemanticModel55
import R1Z.ProverCommitShiftGuards49
/-! Identify all ten shifted semantic polynomials directly with the simulator
payload model. This is a model identity, not native oracle refinement. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticRounds55
open R0P R0P.SemSource R0Z.HonestView R0Z.PayloadSplit R0Z.Shift R0Z.RefPayload
open R1Z.ProverCommitSemanticModel55 Polynomial
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

theorem payload_rounds (pi : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) (r : Fin 10) :
    R0Z.Chain.roundPoly r (shift pub B ch (refPayload (Bat := Bat) pub B ch+L pi B ch t))=
      rounds ch r (oracle pi pub B ch t)+
        if r=9 then C ((fOrig pub B ch t (alpha ch)-fOrig pub B ch 0 (alpha ch))*
          (alpha ch 9-1/2)⁻¹)*(X-C (1/2)) else 0 := by
  rw [shift,map_add,map_smul,original_image,map_add,refPayload,map_add,map_sub,map_smul,
    roundPoly_msCell,R0Z.PureRounds.roundPoly_L,R0Z.Chain.roundPoly_originalRounds,
    R0Z.Chain.roundPoly_dir,original_rounds,k0]
  by_cases hr : r=9
  · simp only [if_pos hr,add_zero,Polynomial.smul_eq_C_mul,map_sub,map_mul]
    ring
  · simp only [if_neg hr,smul_zero,sub_zero,add_zero]
    exact add_comm _ _

theorem shifted_boundary (pi : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) :
    (R0Z.Chain.roundPoly 9 (shift pub B ch (refPayload (Bat := Bat) pub B ch+L pi B ch t))).eval 0+
      (R0Z.Chain.roundPoly 9 (shift pub B ch (refPayload (Bat := Bat) pub B ch+L pi B ch t))).eval 1=
      (rounds ch 9 (oracle pi pub B ch t)).eval 0+(rounds ch 9 (oracle pi pub B ch t)).eval 1 := by
  rw [payload_rounds,if_pos rfl]
  exact ProverCommitShiftGuards49.boundary_preserved _ _ _ (by
    have hn : (2 : K)≠0 := R0Z.Chain.two_ne_zero
    field_simp
    <;> ring)

theorem shifted_terminal (pi : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) (half : alpha ch 9≠1/2) :
    (R0Z.Chain.roundPoly 9 (shift pub B ch (refPayload (Bat := Bat) pub B ch+L pi B ch t))).eval (alpha ch 9)=
      maskLinear pi B (alpha ch) t+fOrig pub B ch t (alpha ch) := by
  rw [payload_rounds,if_pos rfl]
  exact ProverCommitShiftGuards49.terminal_adjustment _ _ _ _ _ _ half
    (terminal_guard pi pub B ch t)

#print axioms payload_rounds
#print axioms shifted_boundary
#print axioms shifted_terminal
end R1Z.ProverCommitSemanticRounds55
