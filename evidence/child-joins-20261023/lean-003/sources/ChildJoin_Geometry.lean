import S2W_ChildJoins
import S2LeadInterface

/-! Downstream multiproof composition and necessary physical scan admission.
Neither theorem constructs upstream physical range observations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ChildJoin_Geometry
open Aeneas Aeneas.Std Result AspisR1Stage2
open S2LeadInterface MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem batches_from_facts {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub ck : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub ck parsed)
    (q : Fin 22 → Fin 262144) :
    (∀ s, (eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q c.nodes 0 s)).2 = true →
      eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q c.nodes 0 s) =
        eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch0)) ∧
    (∀ s, (eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q c.nodes 1 s)).2 = true →
      eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q c.nodes 1 s) =
        eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch1)) :=
  MultiproofConeFrozen2Stage.both_batches (multiproofDigest D) hash H facts.oracle
    parsed q c.nodes facts.nodeViews

theorem scan_short (proof y1 : Slice U8) (short : proof.val.length < 7495) :
    ¬ S2W_ChildJoins.S8StageConeJoin proof y1 := by
  intro join
  have bound := join.scanArgument.1
  omega

/-- The supplied y1 is determined by the physical call, not by a finisher law. -/
theorem scan_unique (proof y1 y2 : Slice U8)
    (one : S2W_ChildJoins.S8StageConeJoin proof y1)
    (two : S2W_ChildJoins.S8StageConeJoin proof y2) : y1 = y2 := by
  exact Result.ok.inj (one.scanArgument.2.symm.trans two.scanArgument.2)

#print axioms batches_from_facts
#print axioms scan_short
#print axioms scan_unique
end AspisR1.ChildJoin_Geometry
end
