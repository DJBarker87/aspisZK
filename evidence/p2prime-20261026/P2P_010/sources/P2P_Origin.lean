import Hist_ArgumentCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_Origin
open Aeneas Aeneas.Std Result S2W_NativeConsolidation
/-- Exact observations erased by SourceCuts: the selected TX2 encoded public
comes from this invocation's validator followed by this invocation's op22. -/
def Fact (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (a2 : S2W_ExtractionBoundary.Accounts) (data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (s : SecondCut) : Prop :=
  ∃ v, AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id a2 data2 slot = ok (.Ok v) ∧
    ops.op22 v.statement = ok (.Ok s.encoded)
end AspisR1.P2P_Origin
end
