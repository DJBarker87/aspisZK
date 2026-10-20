import CuSavingsRetainedQueryPrefixFinishAdapter
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixTx1
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedQueryPrefixBinding CuSavingsRetainedCompositionTx1Transport
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]
  [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1CuRho.HeapReserve]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]

open CuSavingsRetainedQueryPrefixFinishAdapter
attribute [local irreducible] CuSavingsRetainedQueryPrefixFinishAdapter.finish
set_option maxHeartbeats 50000

theorem source_equivalence {H : Type} (prepared : PreparedCommon)
    (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries) (dot : AspisR1RetainedDots.Shared)
    (start len cursor : Usize) (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H) (obs : Option (verifier.Phase→Result Unit)) :
    (letI : PreparedCommon:=CuSavingsRetainedSamplerBinding.binding prepared
     retained.tx1 (finish true common B dot start len cursor) D pub publicBytes proof k hash obs)=
    (letI : PreparedCommon:=CuSavingsRetainedSamplerBinding.binding prepared
     retained.tx1 (finish false common B dot start len cursor) D pub publicBytes proof k hash obs) := by
  letI : PreparedCommon:=CuSavingsRetainedSamplerBinding.binding prepared
  unfold retained.tx1
  split
  · rfl
  · apply (bind_eq_iff _ _ _).mpr
    intro parsed hp
    cases parsed with
    | Err error=>rfl
    | Ok v=>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply (bind_eq_iff _ _ _).mpr
      intro marked hm
      cases marked
      apply (bind_eq_iff _ _ _).mpr
      intro preparation hp
      rcases preparation with ⟨result,g⟩
      simp only [uncurry_apply_pair]
      cases result with
      | Err error=>rfl
      | Ok pair=>
        rcases pair with ⟨claims,p⟩
        have hg:=CuSavingsRetainedQueryPrefixFreshInputs.source_table prepared D pub v hash obs _ g claims p hp
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,uncurry_apply_pair]
        apply (bind_eq_iff _ _ _).mpr
        intro allocated ha
        cases allocated with
        | Err error=>rfl
        | Ok a=>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply (bind_eq_iff _ _ _).mpr
          intro marked hm
          cases marked
          exact finish_eq common B dot start len cursor D v p a g hg publicBytes proof k hash obs

#print axioms source_equivalence
end AspisR1.CuSavingsRetainedQueryPrefixTx1
