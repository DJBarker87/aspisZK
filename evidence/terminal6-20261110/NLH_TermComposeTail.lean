import NKR_TermGatherPoseidon
import NKR_TermSemanticSource
import NKR_TermTail
import NKR_TermHorner
import RPv_JGa_Copy
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermComposeTail
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
/-- Literal emitted237 continuation after its own validation. This is source
support only; native237 and218/261 associations remain mandatory. -/
def run (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) : Result (core.result.Result NKR_TermTail.Carrier NKR_TermTail.Error) := do
 let a ←
   array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
     pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
     field.QM31.ZERO claims
 let a1 ←
   array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
     pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
     field.QM31.ZERO claims
 let a2 ←
   array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
     pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
     field.QM31.ZERO claims
 let mask_only ←
   array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy
     pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
     field.QM31.ZERO claims
 let selectors ←
   pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point
 let sops ←
   pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors
 let poseidon ←
   state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
     { z := a, succ_z := a1, xor12_z := a2 } sops
 let semantic ←
   pool_v1.pair_forest_semantic_terminal.semantic_packed
     pub
     { z := a, succ_z := a1, xor12_z := a2 } selectors
 let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
 let h1_z ←
   pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i
 let pvpfcvv ←
   pool_v1.pair_forest_semantic_terminal.copy_variant pub.variant
 let copy ←
   pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1_z
     selectors lambda chi pub.transition.live_snapshot.next_pair_index
     pvpfcvv
 let prepared_theta ← field.PreparedQm31Multiplier.new theta
 let ii ←
   FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
     semantic
 let iter ←
   core.iter.traits.iterator.Iterator.rev.trait_default
     (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
     field.QM31 24#usize)
     (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
     field.QM31 24#usize) ii
 let composition ←
   pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter
     prepared_theta copy.residual
 let ii1 ←
   FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
     poseidon
 let iter1 ←
   core.iter.traits.iterator.Iterator.rev.trait_default
     (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
     field.QM31 4#usize)
     (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
     field.QM31 4#usize) ii1
 let composition1 ←
   pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
     prepared_theta composition
 let i1 ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
 let q ←
   pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i1
 ok (core.result.Result.Ok (composition1, a, mask_only, q, h1_z,
   copy.active))

def variant : CompiledVariant → pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
 | .PrivateTransfer=>.PrivateTransfer
 | .Withdrawal=>.Withdrawal

theorem variant_source (v : CompiledVariant) : copy_variant v=ok (variant v) := by
 cases v <;> rfl

theorem hcolumn : SELECTED_H1_COLUMN=ok 26#usize := by
 unfold SELECTED_H1_COLUMN POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
 have spec : (16#usize+10#usize : Result Usize) ⦃out=>out.val=26⦄ := by
  step* <;> scalar_tac
 obtain ⟨out,call,value⟩:=WP.spec_imp_exists spec
 have same : out=26#usize := UScalar.eq_of_val_eq value
 exact same ▸ call

/-- Every complete emitted source child in the237 continuation is called at
SAME actual arguments and internally discharged. No supplied success/output
or arbitrary operation dictionary is assumed. Source support only. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (hd : NKR_DigestChildren.Domain pub)
 (hc : canonical claims) (hp : canonical point)
 (hl : Canon lambda) (hchi : Canon chi) (ht : Canon theta)
 (asset : pub.asset_id.val<2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val<2147483647) :
 ∃ out : NKR_TermTail.Carrier, run pub claims point lambda chi theta=ok (.Ok out) ∧
 Canon out.1 ∧ Canon out.2.2.2.1 ∧ Canon out.2.2.2.2.1 ∧ Canon out.2.2.2.2.2 ∧
 canonical out.2.1 ∧ canonical out.2.2.1 := by
 obtain ⟨p,_⟩:=NKR_TermGatherPoseidon.source claims point hc hp
 obtain ⟨sem,sc⟩:=NKR_TermSemanticSource.source pub ⟨p.z,p.succ,p.xor12⟩ p.selectors hd
  p.zCanonical p.succCanonical p.xorCanonical p.selectorHigh p.selectorLow asset amount
 obtain ⟨h1,hcall,ch1⟩:=JFy_SelectedRead.source claims hc 0#usize 26#usize (by decide) (by decide)
 obtain ⟨copy,cc,cr,ca⟩:=JGa_Copy.source p.z h1 p.selectors lambda chi pub.transition.live_snapshot.next_pair_index (variant pub.variant)
  p.zCanonical ch1 p.selectorHigh p.selectorLow hl hchi
 obtain ⟨comp,g,ho,ccomp,cg,_⟩:=NKR_TermHorner.source claims p.z p.mask sem.out p.poseidon theta h1 copy hc sem.canonical_out p.poseidonCanonical ht cr
 refine ⟨(comp,p.z,p.mask,g,h1,copy.active),?_,ccomp,cg,ch1,ca,p.zCanonical,p.maskCanonical⟩
 unfold run
 rw [p.gather0,bind_tc_ok,p.gather1,bind_tc_ok,p.gather2,bind_tc_ok,p.gather3,bind_tc_ok,
  p.selectorCall,bind_tc_ok,p.poseidonSelectorCall,bind_tc_ok,p.poseidonCall,bind_tc_ok,sc,bind_tc_ok,
  hcolumn,bind_tc_ok,hcall,bind_tc_ok,variant_source,bind_tc_ok,cc,bind_tc_ok]
 have mapped : (do let out←NKR_TermHorner.run claims p.z p.mask sem.out p.poseidon theta h1 copy
                   ok (core.result.Result.Ok out : core.result.Result NKR_TermTail.Carrier NKR_TermTail.Error))=
    ok (.Ok (comp,p.z,p.mask,g,h1,copy.active)) := by
   rw [ho,bind_tc_ok]
 simp only [NKR_TermHorner.run,FIv_FoldsTotal.body,bind_assoc_eq,bind_tc_ok] at mapped
 simpa only [FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
   core.iter.traits.iterator.Iterator.rev.trait_default,
   core.iter.traits.iterator.Iterator.rev.default,bind_tc_ok] using mapped
#print axioms variant_source
#print axioms hcolumn
#print source
#print axioms source
end AspisR1.NLH_TermComposeTail
end
