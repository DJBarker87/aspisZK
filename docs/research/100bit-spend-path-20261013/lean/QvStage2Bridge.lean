import QvStage2Count
import QvStage1Bridge
set_option autoImplicit false
namespace AspisR1.QvStage2
open VerifierCallBudget VerifierPhaseCost

theorem distinct_firstReads_bound {Pf : Type}
    (v : AspisV8R19.MemoizedProgramLaw.View Bytes Digest (Pf × Bool))
    (h : CountedTrace 12 v.1) : FS2.distinctFirstReads v ≤ 566 := by
  exact distinctFirstReads_of_totalCalls v 566
    (by simpa only [stage2Budget_twelve] using countedTrace_bound h)

/-- The whole designated core trace, including all rejected and suspended
prefixes, must be supplied by the frozen-source log refinement (R10/R14). -/
def SourceCoverage {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input) (Admitted : Cfg → Input → Prop) : Prop :=
  ∀ cfg input H stop tr, Admitted cfg input → SourcePrefix cfg input H stop tr →
    CountedTrace 12 tr

theorem source_all_prefixes {Cfg Input : Type}
    {SourcePrefix : PrefixRelation Cfg Input} {Admitted : Cfg → Input → Prop}
    (coverage : SourceCoverage SourcePrefix Admitted) :
    AllPrefixCount SourcePrefix Admitted 566 := by
  intro cfg input H stop tr ha hs
  simpa only [stage2Budget_twelve] using
    countedTrace_bound (coverage cfg input H stop tr ha hs)

/-- Reuses only the old hash-step semantics, without its false route budget
or any claim about termination-label refinement. -/
theorem embed_stage2_trace (tr : Trace) (h : CountedTrace 12 tr) :
    Exec (.checkpoint (stage2Budget 12)) tr
      (.checkpoint (stage2Budget 12 - tr.length)) :=
  QvStage1.embed_trace tr _ (countedTrace_bound h)

/-- hQ's verifier-core contribution. No global disjointness of the two
batches or their byte addresses is required. The FS table handles repeats. -/
theorem combined_distinct_firstReads_bound {Pf : Type}
    (v : AspisV8R19.MemoizedProgramLaw.View Bytes Digest (Pf × Bool))
    (tx1 tx2 : Trace) (he : v.1 = tx1 ++ tx2)
    (h1 : QvStage1.CountedTrace 10 tx1) (h2 : CountedTrace 12 tx2) :
    FS2.distinctFirstReads v ≤ verifierBudget := by
  apply distinctFirstReads_of_totalCalls
  rw [he, List.length_append]
  exact Nat.add_le_add (QvStage1.countedTrace_bound h1) (countedTrace_bound h2)

/-- Additional designated observer/adapter/PDA reads must be separately
covered. 1161 is the verifier-core half, not a full Pool syscall budget. -/
theorem combined_with_external_reads {Pf : Type}
    (v : AspisV8R19.MemoizedProgramLaw.View Bytes Digest (Pf × Bool))
    (tx1 tx2 extra : Trace) (q : Nat) (he : v.1 = tx1 ++ tx2 ++ extra)
    (h1 : QvStage1.CountedTrace 10 tx1) (h2 : CountedTrace 12 tx2)
    (hx : extra.length ≤ q) : FS2.distinctFirstReads v ≤ verifierBudget + q := by
  apply distinctFirstReads_of_totalCalls
  rw [he, List.length_append, List.length_append]
  exact Nat.add_le_add
    (Nat.add_le_add (QvStage1.countedTrace_bound h1) (countedTrace_bound h2)) hx

#print axioms distinct_firstReads_bound
#print axioms source_all_prefixes
#print axioms embed_stage2_trace
#print axioms combined_distinct_firstReads_bound
#print axioms combined_with_external_reads
end AspisR1.QvStage2
