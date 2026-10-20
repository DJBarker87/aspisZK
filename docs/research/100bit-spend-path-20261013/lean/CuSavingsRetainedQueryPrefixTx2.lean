import CuSavingsRetainedQueryPrefixFinish
import CuSavingsRetainedResumeWhole
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixTx2
open Aeneas Aeneas.Std Result
open CuSavingsRetainedQueryPrefixBinding
attribute [local irreducible] AspisR1RhoStage.stage_new AspisR1RhoQuery.query_new.query_with_geometry sourcePrefix
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1CuRho.HeapReserve]

private theorem bind_ext {A B : Type} (m : Result A) (f g : A → Result B)
    (h : ∀ x,m=.ok x → f x=g x) : (m >>= f)=(m >>= g) := by
  cases hm : m with
  | fail e => rfl
  | div => rfl
  | ok x => exact h x hm

theorem source_table (tx : AspisR1RhoTransactions.TxCommon) (base : Q.E)
    (hb : CuSavingsRetainedResumeOrigins.ReaderOrigin base) (out : G)
    (hp : letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
          AspisR1RhoTransactions.weights.powers 29#usize base=.ok out) : SourceTable out := by
  have origin:=CuSavingsRetainedResumeDotBinding.input_origin base hb
  obtain ⟨source,hs,ho⟩:=CuSavingsRetainedResumeDotBinding.powers_success tx 29#usize base out hp
  subst out
  intro i hi
  have h:=CuSavingsCanonicalDotsSources.SourceValue.power 29#usize
    (CuSavingsRetainedResumeDotBinding.input base) source i hi origin hs
  simpa only [CuSavingsRetainedResumeDotBinding.table,List.getElem_map,
    CuSavingsRetainedResumeDotBinding.input,CuSavingsRetainedResumeDotBinding.fromInput] using h

theorem tx2_equivalence {H : Type} (tx : AspisR1RhoTransactions.TxCommon)
    (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries) (dot : AspisR1RetainedDots.Shared)
    (resumeB : CuSavingsRetainedResumeBinding.Boundaries) (D : Q.D H)
    (publicBytes proof checkpoint1 : Slice U8) (hash : H) (obs : Option (Q.Phase→Result Unit)) :
    (letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
     letI : AspisR1RhoResumeCaller.ResumeCommon:=CuSavingsRetainedResumeBinding.binding resumeB
     letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoTransactions.tx_new.tx2 D publicBytes proof checkpoint1 hash obs) =
    (letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
     letI : AspisR1RhoResumeCaller.ResumeCommon:=CuSavingsRetainedResumeBinding.binding resumeB
     letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoTransactions.tx_new.tx2 D publicBytes proof checkpoint1 hash obs) := by
  letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
  letI : AspisR1RhoResumeCaller.ResumeCommon:=CuSavingsRetainedResumeBinding.binding resumeB
  unfold AspisR1RhoTransactions.tx_new.tx2
  apply bind_ext
  intro parsed hp
  cases parsed with
  | Err error=>simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  | Ok v=>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply bind_ext
    intro marked hm
    cases marked
    apply bind_ext
    intro resumed hr
    cases resumed with
    | Err error=>simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    | Ok pair=>
      rcases pair with ⟨p,a⟩
      have origin:=(CuSavingsRetainedResumeWhole.source_inputs resumeB D checkpoint1 proof publicBytes v.variant hash p a hr).1
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,uncurry_apply_pair]
      apply bind_ext
      intro g hg
      have hsource:=source_table tx p.gamma origin g hg
      simp only [CuSavingsRetainedQueryPrefixStage.stage_eq common B dot D v p a g hsource hash obs,
        AspisR1RhoTransactions.stage_new]

theorem tx2_authenticated_equivalence {H : Type} (tx : AspisR1RhoTransactions.TxCommon)
    (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries) (dot : AspisR1RetainedDots.Shared)
    (resumeB : CuSavingsRetainedResumeBinding.Boundaries) (D : Q.D H)
    (publicBytes proof checkpoint1 : Slice U8) (hash : H) (obs : Option (Q.Phase→Result Unit)) :
    (letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
     letI : AspisR1RhoResumeCaller.ResumeCommon:=CuSavingsRetainedResumeBinding.binding resumeB
     letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoTransactions.tx_new.tx2_authenticated D publicBytes proof checkpoint1 hash obs) =
    (letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
     letI : AspisR1RhoResumeCaller.ResumeCommon:=CuSavingsRetainedResumeBinding.binding resumeB
     letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoTransactions.tx_new.tx2_authenticated D publicBytes proof checkpoint1 hash obs) := by
  letI : AspisR1RhoTransactions.TxCommon:=CuSavingsRetainedResumeDotBinding.binding tx
  letI : AspisR1RhoResumeCaller.ResumeCommon:=CuSavingsRetainedResumeBinding.binding resumeB
  unfold AspisR1RhoTransactions.tx_new.tx2_authenticated
  apply bind_ext
  intro parsed hp
  cases parsed with
  | Err error=>simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  | Ok v=>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply bind_ext
    intro marked hm
    cases marked
    apply bind_ext
    intro resumed hr
    cases resumed with
    | Err error=>simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    | Ok pair=>
      rcases pair with ⟨p,a⟩
      have origin:=(CuSavingsRetainedResumeWhole.source_inputs resumeB D checkpoint1 proof publicBytes v.variant hash p a hr).1
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,uncurry_apply_pair]
      apply bind_ext
      intro g hg
      have hsource:=source_table tx p.gamma origin g hg
      simp only [CuSavingsRetainedQueryPrefixStage.stage_eq common B dot D v p a g hsource hash obs,
        AspisR1RhoTransactions.stage_new]

#print axioms source_table
#print axioms tx2_equivalence
#print axioms tx2_authenticated_equivalence
end AspisR1.CuSavingsRetainedQueryPrefixTx2
