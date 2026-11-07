import LIBB_C04StoppedTrace
import NLT_C04Installed
import NLT_Chronology
set_option autoImplicit false
noncomputable section
namespace LIBB_C04DetailGraph
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Separate native/detail bridge. The eventual field is defined from the
source plan, never from this relation or from a selected native execution. -/
def RenderLaw (H : Bytes → State) : {e : NJU_CommonObserved.Event} →
 (detail : NLT_Subcuts.Detail H e) → NNC_DigestTrace.Trace → Prop
 | _,.ordinary _ _,trace => NNC_DigestTrace.render trace = []
 | _,.returning pr p folded reply inside out _,trace =>
   NNC_DigestTrace.render trace = LIBB_C04LogGraph.render
    (NLP_C04Chronology.atEvent H (.merkle pr p folded reply))
 | _,.aborting pr p folded error inside pending _,trace =>
   NNC_DigestTrace.render trace = LIBB_C04LogGraph.render (inside ++ pending.answered) ∧
   NLL_Prefix.At (NLP_C04Chronology.atEvent H (.merkle pr p folded (.fail error)))
    (inside ++ pending.answered) pending.parts

/-- The supplied law is the one NMN_064.root discharges for each SAME native
record; it is an intermediate premise here, not an added row/caller clause. -/
theorem transport {H : Bytes → State} {e : NJU_CommonObserved.Event}
 (detail : NLT_Subcuts.Detail H e) (law : NLT_C04Installed.Law H detail)
 (trace : NNC_DigestTrace.Trace) (observed : NNC_C04Trace.FromDetail detail trace) :
 RenderLaw H detail trace := by
 cases detail with
 | ordinary e notMerkle =>
   change trace = [] at observed
   subst trace
   rfl
 | returning pr p folded reply inside out child =>
   obtain ⟨log,native,rfl⟩ := observed
   exact (LIBB_C04RichTrace.returned native).trans
    (congrArg LIBB_C04LogGraph.render law.2.1.symm)
 | aborting pr p folded error inside pending child =>
   obtain ⟨log,native,rfl⟩ := observed
   exact ⟨LIBB_C04StoppedTrace.stopped native,law.1⟩

/-- Every completed detail has exactly its deterministic source trace, even
when the verifier returns a rejection. No child-Ok premise is required. -/
theorem completed {H : Bytes → State} {e : NJU_CommonObserved.Event}
 (detail : NLT_Subcuts.Detail H e) (law : NLT_C04Installed.Law H detail)
 (trace : NNC_DigestTrace.Trace) (observed : NNC_C04Trace.FromDetail detail trace)
 (history : NLL.History) (done : NLT_Chronology.history detail = some history) :
 NNC_DigestTrace.render trace = LIBB_C04LogGraph.render (NLP_C04Chronology.atEvent H e) := by
 have h := transport detail law trace observed
 cases detail with
 | ordinary e notMerkle =>
   have no : NLP_C04Chronology.atEvent H e = [] := by
     cases e <;> try rfl
     exact False.elim (notMerkle _ _ _ _ rfl)
   exact h.trans (congrArg LIBB_C04LogGraph.render no.symm)
 | returning pr p folded reply inside out child => exact h
 | aborting pr p folded error inside pending child => cases done
#print axioms transport
#print axioms completed
end LIBB_C04DetailGraph
end
