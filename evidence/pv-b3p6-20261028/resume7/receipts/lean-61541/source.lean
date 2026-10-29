import PV_B3P_CopyBasicsSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- All136 immutable links carry valid producer/consumer bounds. The proof
composes both restored writes at each symbolic step, without executing the loop. -/
theorem copy_loop_total (selectors : reference_copy_terminal.Selectors) (append_index : U64)
    (variant : reference_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (patterns : Array aspis_core.field.QM31 14#usize)
    (a b c d : Array aspis_core.field.QM31 2#usize) (link_index : Usize)
    (hi : link_index.val≤136) :
    Success (reference_copy_terminal.evaluate_with_selectors_loop selectors append_index variant patterns a b c d link_index) := by
  have hw : reference_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1=136#usize := by
    unfold reference_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1
    rfl
  unfold reference_copy_terminal.evaluate_with_selectors_loop
  refine loop_total _ (fun x : Array aspis_core.field.QM31 2#usize × Array aspis_core.field.QM31 2#usize × Array aspis_core.field.QM31 2#usize × Array aspis_core.field.QM31 2#usize × Usize => 136-x.2.2.2.2.val)
    (fun x => x.2.2.2.2.val≤136) ?_ (a,b,c,d,link_index) hi
  rintro ⟨v,w,v1,w1,i⟩ hi
  change i.val≤136 at hi
  by_cases hlt : i.val<136
  · have hb : i<136#usize := by scalar_tac
    have hlen : i.val<reference_copy_terminal.constants.COPY_LINKS.val.length := by
      rw [reference_copy_terminal.constants.COPY_LINKS.property]
      exact hlt
    let link := reference_copy_terminal.constants.COPY_LINKS.val[i.val]'hlen
    have hlink := PV_B3P_SelectIndex227.index_value reference_copy_terminal.constants.COPY_LINKS i hlt
    have hsafe : LinkSafe link := links_safe link (List.getElem_mem hlen)
    obtain ⟨weight,hweight⟩ := weight_total link append_index variant hsafe.1
    obtain ⟨⟨v2,w2⟩,hproducer⟩ := endpoint_total v w link.producer link.tag weight patterns selectors hsafe.2.1
    obtain ⟨⟨v3,w3⟩,hconsumer⟩ := endpoint_total v1 w1 link.consumer link.tag weight patterns selectors hsafe.2.2
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    simp only [link] at hweight hproducer hconsumer
    refine ⟨.cont (v2,w2,v3,w3,j),?_,?_,?_⟩
    · simp only [reference_copy_terminal.evaluate_with_selectors_loop.body,hw,hb,↓reduceIte,
        hlink,hweight,hproducer,hconsumer,lift,bind_tc_ok,j]
    · change j.val≤136
      omega
    · change 136-j.val<136-i.val
      omega
  · have hb : ¬i<136#usize := by scalar_tac
    refine ⟨.done (v,w,v1,w1),?_,True.intro⟩
    simp only [reference_copy_terminal.evaluate_with_selectors_loop.body,hw,hb,↓reduceIte]

#print axioms copy_loop_total
end PV_B3P_Success227
