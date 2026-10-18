import R1Z.IIPrimeR1
import R1Z.ClauseIR1

/-! J16-R1 (DESIGN-R1-PRIVACY-MODEL §3.6, §4; LOG D39): the R1 privacy
statement for the prover restricted to valid instances.

* `maskImageOn_R1`: `MaskImageOn P_R1` for `h.restrict (ValidOn P_R1 h B x)`,
  from clause (i′) (`clause_i_R1_all`) and clause (ii′) (`iiPrime_R1`) through
  `maskImageOn_restrict_of`.
* `hvzk_R1`: perfect HVZK on `P_R1` (`hvzk_on_restrict`).
* `zkfs_R1_abort`, `zkfs_R1_abort_terms`: the ZF1-abort hand-off, ZK_FS for the
  retrying restricted prover with error `ε_real + ε_ideal`, resp.
  `ε_hit + ε_coll + ε_prog`; the reduction and the two couplings are
  hypotheses.

Premises on the statement: `PackField B`, `PublicBase F x.1`, and base-typed
honest instances.  Every challenge condition is a conjunct of `P_R1`. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.MaskImageR1
open R0P R0Z.HonestView R0Z.D12 R0Z.Shift R1Z.Batched R1Z.PredicateR1

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The R1 prover restricted to the instances valid for every `P_R1` challenge. -/
abbrev validR1 (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (x : Statement K CommitHandle) : HonestProver K :=
  R0Z.ZkStatement.HonestProver.restrict h (R0Z.HonestValid.ValidOn (P_R1 h.transport B hB) h B x)

/-- DESIGN-R1-PRIVACY-MODEL §3.6: both clauses of `MaskImageOn` on R1. -/
theorem maskImageOn_R1 (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w)) :
    MaskImageOn (Bat := R1Bat) (P_R1 h.transport B hB) (validR1 h B hB x) B x :=
  R0Z.HonestValid.maskImageOn_restrict_of (P_R1 h.transport B hB) h B x
    (R1Z.ClauseIR1.clause_i_R1_all h B hB x hpub hF)
    (R1Z.IIPrimeR1.iiPrime_R1 h B hB x hpub hF)

/-- Perfect HVZK on `P_R1` for the restricted R1 prover. -/
theorem hvzk_R1 (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w)) :
    HVZK_on (Bat := R1Bat) (P_R1 h.transport B hB) (validR1 h B hB x) B outputs x :=
  R0Z.HonestValid.hvzk_on_restrict (P_R1 h.transport B hB) h _ B outputs x
    (maskImageOn_R1 h B hB x hpub hF)

/-- ZF1-abort Theorem A on R1. -/
theorem zkfs_R1_abort (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : R0Z.FsStatement.FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w))
    (ab : R0Z.FsAbort.AbortBridge K CommitHandle Aux R1Bat fs.Adversary) (ε_real ε_ideal : ℚ)
    (hr : R0Z.FsAbort.AbortReductionWith (P_R1 h.transport B hB) (validR1 h B hB x) B outputs fs ab x
      ε_real ε_ideal) :
    R0Z.FsStatement.ZK_FS (validR1 h B hB x) B outputs fs x (ε_real + ε_ideal) :=
  R0Z.HonestValid.zkfs_restrict_abort (P_R1 h.transport B hB) h _ B outputs fs x ab ε_real ε_ideal
    (maskImageOn_R1 h B hB x hpub hF) hr

/-- ZF1-abort Theorem B on R1: error `ε_hit + ε_coll + ε_prog`, with the real
(Hit, Coll) and ideal (Prog) couplings as hypotheses. -/
theorem zkfs_R1_abort_terms (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : R0Z.FsStatement.FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w))
    (ab : R0Z.FsAbort.AbortBridge K CommitHandle Aux R1Bat fs.Adversary) (ε_hit ε_coll ε_prog : ℚ)
    (h0 : 0 ≤ ε_hit) (h1 : 0 ≤ ε_coll) (h2 : 0 ≤ ε_prog)
    (hreal : R0Z.FsAbort.RealAbortCoupling (P_R1 h.transport B hB) (validR1 h B hB x) B outputs fs ab x
      ε_hit ε_coll)
    (hideal : R0Z.FsAbort.IdealAbortCoupling (P_R1 h.transport B hB) (validR1 h B hB x) B outputs fs ab
      x ε_prog) :
    R0Z.FsStatement.ZK_FS (validR1 h B hB x) B outputs fs x (ε_hit + ε_coll + ε_prog) :=
  R0Z.HonestValid.zkfs_restrict_abort_terms (P_R1 h.transport B hB) h _ B outputs fs x ab
    ε_hit ε_coll ε_prog h0 h1 h2 (maskImageOn_R1 h B hB x hpub hF) hreal hideal

#print axioms validR1
#print axioms maskImageOn_R1
#print axioms hvzk_R1
#print axioms zkfs_R1_abort
#print axioms zkfs_R1_abort_terms
end R1Z.MaskImageR1
