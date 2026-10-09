import R0P.MaskValue
import R0P.MaskMaxErr

/-! G25 concrete soundness instance of the reference claim-dependent mask. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemDegree
noncomputable section
variable {K : Type} [Field K] {F : Subfield K}

/-- The verifier reads the original point mask and lane 28's extra Libra claim. -/
abbrev maskValueClaims (B : PackBasis F) := maskClaimsR0 B

theorem maskValueClaims_degree (B : PackBasis F) : MaskDegree (maskValueClaims B) := by
  intro π t
  exact maskClaimsR0_vdeg B π t

#print axioms maskValueClaims
#print axioms maskValueClaims_degree
end
end R0P.Mask

namespace R0P.Mask
open R0C.SlackStatement
open FS FS2 FS2.Duplex R0C.V3 R0P.SemSource R0P.SemD3Glue R0P.MaskDuplex AspisWideTower
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {Sfield : Fin 29 → Subfield WideExact} {Pf : Type} {L : Nat}
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
variable (msg : Pf → Nat → MsgZ WideExact)
local notation "prZ" => combinedProtocolZ B p msg (fun _ _ => none)
local notation "VZ" => FS2.verifier (prZ) (combinedDecisionZ (maskValueClaims B) B)

/-- D14″ and D14′ opening budgets, recorded before taking the q22 maximum. -/
theorem masked_opening_budget_exact :
    R0FS.ε WideExact 0 = (336869026605739 + 16800 : ℚ) / ((Fintype.card WideExact : ℚ) - 1) ∧
    R0FS.ε WideExact 1 = (400 : ℚ) / (Fintype.card WideExact : ℚ) := ⟨rfl, rfl⟩

#print axioms masked_opening_budget_exact

/-- The reference mask evaluated from the opened claims, with its degree obligation discharged. -/
theorem combined_fiat_shamir_masked (x : TypedContext WideExact Sfield) (hr32 : p.rounds = 32)
    (hσsem : ∀ (i : Nat) (_hi : i < 25) (s : State),
      p.σ i s = R0C.SemStatement.Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 25 s = R0C.SemStatement.Chal.circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 26 s = R0C.SemStatement.Chal.circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (27+j.val) s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ j.val s))
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VZ) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (FS2.accepts (eval H (FS2.experiment P (VZ) x)) ∧
        FS2.extractFails (prZ) x (eval H (FS2.experiment P (VZ) x)))) ≤
      (Qtot : ℚ) * ((1 + delta0) *
        ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))) + κ Qtot := by
  exact combined_fiat_shamirZ_closed (maskValueClaims B) (maskValueClaims_degree B)
    B p msg x hr32 hσsem hσz0 hσz1 hσopen P Qtot hQ

#print axioms combined_fiat_shamir_masked
end
end R0P.Mask
