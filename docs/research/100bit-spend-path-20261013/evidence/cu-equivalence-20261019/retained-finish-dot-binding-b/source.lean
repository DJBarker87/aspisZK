import CuSavingsRetainedFinishDotClients
import CuSavingsRetainedFinishBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.CuSavingsRetainedFinishDotBinding
open Aeneas Aeneas.Std Result
open CuSavingsRetainedFinishRelation CuSavingsRetainedFinishDotClients
/-- Source-call fission frames for the exact ordinary/shared point-row region,
final enumerate region and the same regions on non-S2 fallback paths. Each
frame is a computational source context; it has no proposition fields. -/
structure Frames (State : Type) where
  point : Clients→AspisR1S2Groups.Weights→AspisR1RhoResumeCaller.verifier.Prepared→Slice U8→
    CuSavingsRetainedCompositionWeightsInputs.Parts→CuSavingsRetainedCompositionWeightsInputs.Parts→
    Result (core.result.Result State AspisR1RhoResumeCaller.verifier.Error)
  finalTail : Clients→AspisR1RhoTransactions.verifier.View→AspisR1RhoResumeCaller.verifier.Prepared→
    AspisR1RhoResumeCaller.verifier.Accumulator→Option (AspisR1RhoTransactions.verifier.Phase→Result Unit)→
    AspisR1RhoResumeCaller.aspis_core.field.WideExact→AspisR1RhoResumeCaller.aspis_core.field.WideExact→
    Result (core.result.Result Unit AspisR1RhoResumeCaller.verifier.Error)
  fallback : Clients→AspisR1RhoTransactions.verifier.View→AspisR1RhoResumeCaller.verifier.Prepared→
    AspisR1RhoResumeCaller.verifier.Accumulator→Option (AspisR1RhoTransactions.verifier.Phase→Result Unit)→
    Result (core.result.Result Unit AspisR1RhoResumeCaller.verifier.Error)

def boundaries {State : Type} (frame : Frames State) (base : Boundaries State)
    (clients : Clients) : Boundaries State :=
  {base with pointPrefix:=frame.point clients,finalTail:=frame.finalTail clients,fallback:=frame.fallback clients}

variable [AspisR1CanonicalDots.Shared]
theorem boundaries_equivalence {State : Type} (frame : Frames State) (base : Boundaries State) :
    boundaries frame base newClients=boundaries frame base oldClients :=
  congrArg (boundaries frame base) clients_equivalence

variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared]
/-- The actual TxCommon dictionary is equal, rather than assuming equality of
an enclosing transaction or its children. Thus every source caller may use it. -/
theorem binding_equivalence {State : Type} (frame : Frames State) (base : Boundaries State)
    (newer : Bool) (common : AspisR1RhoTransactions.TxCommon) :
    CuSavingsRetainedFinishBinding.binding newer (boundaries frame base newClients) common=
      CuSavingsRetainedFinishBinding.binding newer (boundaries frame base oldClients) common :=
  congrArg (fun b=>CuSavingsRetainedFinishBinding.binding newer b common)
    (boundaries_equivalence frame base)

theorem source_finish_equivalence {State : Type} (frame : Frames State) (base : Boundaries State)
    (newer : Bool) (v : AspisR1RhoTransactions.verifier.View)
    (p : AspisR1RhoResumeCaller.verifier.Prepared) (a : AspisR1RhoResumeCaller.verifier.Accumulator)
    (obs : Option (AspisR1RhoTransactions.verifier.Phase→Result Unit)) :
    CuSavingsRetainedFinishBinding.sourceFinish newer (boundaries frame base newClients) v p a obs=
      CuSavingsRetainedFinishBinding.sourceFinish newer (boundaries frame base oldClients) v p a obs :=
  congrArg (fun b=>CuSavingsRetainedFinishBinding.sourceFinish newer b v p a obs)
    (boundaries_equivalence frame base)

/-- Applies in particular to complete fresh and resumed source callers, with
all preparation/resume/field-read failures retained. The dictionaries are
already globally equal; no successful-producer premise is needed. -/
theorem complete_caller_context {State T : Type} (frame : Frames State) (base : Boundaries State)
    (newer : Bool) (common : AspisR1RhoTransactions.TxCommon)
    (caller : AspisR1RhoTransactions.TxCommon→Result T) :
    caller (CuSavingsRetainedFinishBinding.binding newer (boundaries frame base newClients) common)=
      caller (CuSavingsRetainedFinishBinding.binding newer (boundaries frame base oldClients) common) :=
  congrArg caller (binding_equivalence frame base newer common)

#print axioms boundaries_equivalence
#print axioms binding_equivalence
#print axioms source_finish_equivalence
#print axioms complete_caller_context
end AspisR1.CuSavingsRetainedFinishDotBinding
