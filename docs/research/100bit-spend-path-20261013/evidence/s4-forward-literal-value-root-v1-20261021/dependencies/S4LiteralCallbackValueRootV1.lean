import S4LiteralHeadSumRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsLiteralCallbackValueRootV1
open AspisR1FastDotsQueryValuesFourCallbackFieldResultV2 (Ops CurrentWide CallbackFieldResult)
open AspisR1FastDotsLiteralHeadSumRootV1 (headTermValue source_head_sum_literal)
/-- The head summation has fixed source indices and literal byte reads; no
execution-selected head contribution list remains in the value equation.
The retained tail trace still ties all three tail factors to their actual reads. -/
def LiteralFieldResult (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array CurrentWide 29#usize) (slot : Usize) (value : CurrentWide) : Prop :=
  ∃ (wide28 : CurrentWide) (q : AspisR1EbyKPushDotBackend.PushQm)
    (tailStart tail2 : AspisR1EbyKPushDotBackend.PushState)
    (cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution),
    AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q ∧
    Array.index_usize g 28#usize=.ok wide28 ∧
    AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot
      {start:=0#usize,«end»:=2#usize} tailStart tail2 cs ∧
    AspisR1DotCountBoundV1.AcceptedPushTrace
      AspisR1FastDotsPushProductTraceRootV1.raw EbyKNewToPushStateABI.pushZero
      ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 ∧
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value)=
      ((List.range' 0 26).map (headTermValue a g slot.val)).sum +
      (((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))).map
        (fun p=>AspisR1FastDotsTailFieldProductRootV1.wideDecoded p.1 *
          AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum

theorem callback_field_result_literal (base ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array CurrentWide 29#usize) (slot : Usize) (value : CurrentWide)
    (h : CallbackFieldResult base ops a g slot value) :
    LiteralFieldResult ops a g slot value := by
  rcases h with ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
    _hcallback,_htrace,_hlen,hindices,hmeaning,hfirst,hwide,hrun,haccepted,hdecode⟩
  have hhead := source_head_sum_literal a g slot ds.flatten hindices hmeaning
  rw [hhead] at hdecode
  exact ⟨wide28,q,tailStart,tail2,cs,hfirst,hwide,hrun,haccepted,hdecode⟩
#print axioms callback_field_result_literal
end AspisR1FastDotsLiteralCallbackValueRootV1
