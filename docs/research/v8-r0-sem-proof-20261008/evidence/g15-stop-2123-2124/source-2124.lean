import R0P.SemD3Glue
set_option autoImplicit false
open FS FS2 FS2.Duplex R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement
open AspisWideTower AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
noncomputable section
/-- Diagnostic only: expose the missing G14 obligations without assuming them. -/
example (prime : Nat) [CharP SemE prime] (hprime : prime = 2^31-1)
    {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (msg : Pf → Nat → Msg SemE SemE (SemMsg SemE))
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext SemE Sfield) (Msg SemE SemE (SemMsg SemE))
        (Duplex.Chal (Chal SemE SemE)) × Msg SemE SemE (SemMsg SemE) ×
          Duplex.Chal (Chal SemE SemE))))
    (budget : Nat → ℚ)
    (hσ26 : ∀ s, p.σ 26 s = .opening (R0C.V3.DQ.σQ 0 s)) :
    FS2.D3 (combinedProtocol B p msg decode) (duplexRows B budget)
      (FS2.verifier (combinedProtocol B p msg decode) (combinedDecision B)) := by
  apply R0P.SemD3Glue.d3 prime hprime B p msg decode budget hσ26
end
