import R3SemanticEquationCore

/-! The typed field-checking verifier does evaluate semantic constraints.
This theorem deliberately does not identify that verifier with the free byte
decision d used by R19: that source/representation refinement is still owed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R3MaskedDecisionProjection
open R0P R0P.Mask R0P.SemSource
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Actual typed semantic-decision acceptance supplies its own successfully
parsed polynomials, claim and field checks, on the very same typed prefix. -/
theorem accepted_checks {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (B : PackBasis F)
    (P : R0C.SemStatement.Prefix K K (TypedContext K Sfield) (SemMsgZ K)) (m : MsgZ K)
    (h : decisionZ maskClaims B P m = true) :
    ∃ (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
      (cs : List K) (hcs : cs.length = 25)
      (polys : Fin 10 → Polynomial K) (claim : K),
      openingViewZ P = some Q ∧
      semChalsZ (P.rounds.take 25) = some cs ∧
      semPolysZ (P.rounds.take 25) = some polys ∧
      claimOf P.rounds = some claim ∧
      sumcheckChecksZ maskClaims P.statement.pub B
        (fun j => cs[j.val]'(by omega)) (cs[14]'(by omega)) claim
        (fun j => cs[15 + j.val]'(by omega)) polys
        Q.statement.pointClaims P.statement.extraClaims := by
  unfold decisionZ at h
  split at h
  · rename_i hw
    obtain ⟨Q,cs,hcs,polys,claim,om,hview,hchals,hpolys,hclaim,hchecks,_⟩ := hw
    exact ⟨Q,cs,hcs,polys,claim,hview,hchals,hpolys,hclaim,hchecks⟩
  · cases h

#print axioms accepted_checks
end AspisR1.R3MaskedDecisionProjection
end
