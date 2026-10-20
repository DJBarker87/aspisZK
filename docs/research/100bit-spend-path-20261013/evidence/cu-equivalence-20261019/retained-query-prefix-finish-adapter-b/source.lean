import CuSavingsRetainedQueryPrefixFreshInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixFinishAdapter
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedQueryPrefixBinding CuSavingsRetainedCompositionTx1Transport
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]
  [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1CuRho.HeapReserve]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]

def finish (isNew : Bool) (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) (start len cursor : Usize) : Finish :=
  letI : AspisR1RhoQuery.QueryCommon:=if isNew then newBinding common B dot else oldBinding common B dot
  finishNew start len cursor
attribute [local irreducible] finish CuSavingsRhoAllocationSuccess.raw4Backend
set_option maxHeartbeats 50000

theorem finish_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) (start len cursor : Usize)
    {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (g : Array aspis_core.field.WideExact 29#usize)
    (hg : SourceTable (CuSavingsRhoEntryTransport.array CuSavingsRhoEntryTransport.wide g))
    (publicBytes proof : Slice U8) (k : Usize) (hash : H) (obs : Option (verifier.Phase→Result Unit)) :
    finish true common B dot start len cursor D v p a g publicBytes proof k hash obs=
      finish false common B dot start len cursor D v p a g publicBytes proof k hash obs := by
  letI : AspisR1CuRho.HeapReserve:=CuSavingsRhoEmptyReserveModel.heapReserve
    (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
  unfold finish finishNew
  rw [CuSavingsRetainedQueryPrefixFinish.tx1_finish_eq common B dot (digest D) (view v)
    (CuSavingsRhoEntryTransport.prepared p) (CuSavingsRhoEntryTransport.accumulator a)
    (CuSavingsRhoEntryTransport.array CuSavingsRhoEntryTransport.wide g) hg publicBytes proof k hash obs]

#print axioms finish_eq
end AspisR1.CuSavingsRetainedQueryPrefixFinishAdapter
