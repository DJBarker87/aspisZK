import CuSavingsRetainedQueryPrefixStage
import AspisR1RhoTransactions.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixFinish
open Aeneas Aeneas.Std Result
open CuSavingsRetainedQueryPrefixBinding CuSavingsRetainedQueryPrefixStage
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1CuRho.HeapReserve]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]

theorem tx1_finish_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) {H : Type} (D : Q.D H) (v : Q.View)
    (p : Q.Prepared) (a : AspisR1RhoQuery.verifier.Accumulator) (g : G) (hg : SourceTable g)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H) (obs : Option (Q.Phase→Result Unit)) :
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoTransactions.tx_new.tx1_finish D v p a g publicBytes proof k hash obs) =
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoTransactions.tx_new.tx1_finish D v p a g publicBytes proof k hash obs) := by
  unfold AspisR1RhoTransactions.tx_new.tx1_finish
  simp only [AspisR1RhoTransactions.stage_new,stage_eq common B dot D v p a g hg hash obs]

#print axioms tx1_finish_eq
end AspisR1.CuSavingsRetainedQueryPrefixFinish
