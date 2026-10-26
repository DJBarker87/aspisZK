import P2P_Origin
import Hiq_Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_NativeSelection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Deterministic byte selection from the native entries, independent of H.
It makes no assumption that a separately supplied account adversary chose them. -/
def pair (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (e1 e2 : Entry) (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  (⟨(Hiq_ByteSelection.account ops e1.first 0#usize).drop 688,
      Hiq_ByteSelection.account ops e1.first 1#usize⟩,
   ⟨(Hiq_ByteSelection.account ops (e2.second secondSizes) 0#usize).drop 688,
      Hiq_ByteSelection.public2 ops id (e2.second secondSizes) data2 slot⟩)

theorem on_cuts (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (e1 e2 : Entry) (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops e1.first (e2.second secondSizes) saved f s)
    (origin : P2P_Origin.Fact ops id (e2.second secondSizes) data2 slot s) :
    pair ops id e1 e2 data2 slot = Hist_PairExperiment.select ⟨f,s⟩ := by
  obtain ⟨v,validate,encode⟩ := origin
  obtain ⟨proof1,public1⟩ := Hiq_Suffix.first _ _ _ _ _ _ cuts
  have proof2 := Hiq_Suffix.second _ _ _ _ _ _ cuts
  have public2 := Hiq_ByteSelection.public2_read _ _ _ _ _ _ _ validate encode
  simp only [pair,Hist_PairExperiment.select,proof1,public1,proof2,public2]
  rfl

#print axioms on_cuts
end AspisR1.P2P_NativeSelection
end
