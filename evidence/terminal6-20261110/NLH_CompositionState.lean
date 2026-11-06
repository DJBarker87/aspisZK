import NKI_InitialPrefix
import NJB_ArrayCarrier
import NLH_FoldRust
import NKR_TermGatherPoseidon
import NKR_TermTail
import NKR_TermHorner
import NJB_PreparedCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompositionState
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
abbrev Error := PoolV1PairForestSemanticTerminalErrorV1
structure State where
 openings : Openings
 mask : Array NQ 10#usize
 selectors : Selectors
 poseidonSelectors : state_only_poseidon.StateOnlyPoseidonSelectors
 poseidon : Array NQ 4#usize
 semantic : Array NQ 24#usize
 h : NQ
 copyVariant : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
 copy : NKR_TermHorner.Copy
 prepared : FIv_PreparedNew.NP
 composition : NQ
 remaining : List NQ
 g : NQ
inductive Event where
 | amount | validate | gather (i : Fin 4) | selectors | poseidonSelectors
 | poseidon | semantic | h | variant | copy | prepare | horner (i : Fin 28) | g
/-- ONE parent state; every gathered array, callee result and loop accumulator
is read from the preceding state at the frozen call occurrence. -/
def step (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) : Event → State → Result (core.result.Result State Error)
 | .amount, st =>
   match pub.withdrawal_amount with
   | none => ok (.Ok st)
   | some a => if a=0#u32 ∨ 1073741824 ≤ a.val then ok (.Err .InvalidPublicAmount) else ok (.Ok st)
 | .validate, st => do
   let r ← validate_transition pub
   match r with
   | .Err e => ok (.Err e)
   | .Ok _ => ok (.Ok st)
 | .gather i, st =>
   match i.val with
   | 0 => do
     let a ← array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
       composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims
     ok (.Ok {st with openings := {st.openings with z := a}})
   | 1 => do
     let a ← array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
       composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims
     ok (.Ok {st with openings := {st.openings with succ_z := a}})
   | 2 => do
     let a ← array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
       composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims
     ok (.Ok {st with openings := {st.openings with xor12_z := a}})
   | _ => do
     let a ← array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy
       composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims
     ok (.Ok {st with mask := a})
 | .selectors, st => do
   let selectors ← pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point
   ok (.Ok {st with selectors := selectors})
 | .poseidonSelectors, st => do
   let selectors ← poseidon_selectors st.selectors
   ok (.Ok {st with poseidonSelectors := selectors})
 | .poseidon, st => do
   let poseidon ← state_only_poseidon.evaluate_state_only_poseidon_oracle_projected st.openings st.poseidonSelectors
   ok (.Ok {st with poseidon := poseidon})
 | .semantic, st => do
   let semantic ← semantic_packed pub st.openings st.selectors
   ok (.Ok {st with semantic := semantic})
 | .h, st => do
   let column ← SELECTED_H1_COLUMN
   let h ← selected_claim claims 0#usize column
   ok (.Ok {st with h := h})
 | .variant, st => do
   let v ← copy_variant pub.variant
   ok (.Ok {st with copyVariant := v})
 | .copy, st => do
   let copy ← pool_v1.pair_forest_copy_terminal.evaluate_with_selectors st.openings.z st.h st.selectors
     lambda chi pub.transition.live_snapshot.next_pair_index st.copyVariant
   ok (.Ok {st with copy := copy})
 | .prepare, st => do
   let prepared ← field.PreparedQm31Multiplier.new theta
   ok (.Ok {st with prepared := prepared, composition := st.copy.residual, remaining := st.semantic.val.reverse ++ st.poseidon.val.reverse})
 | .horner _, st =>
   match st.remaining with
   | [] => fail .panic
   | lane::rest => do
     let product ← field.PreparedQm31Multiplier.mul st.prepared st.composition
     let value ← field.QM31.add product lane
     ok (.Ok {st with composition := value, remaining := rest})
 | .g, st => do
   let column ← SELECTED_G_COLUMN
   let g ← selected_claim claims 0#usize column
   ok (.Ok {st with g := g})
def order : List Event := [.amount,.validate] ++ (List.finRange 4).map Event.gather ++
 [.selectors,.poseidonSelectors,.poseidon,.semantic,.h,.variant,.copy,.prepare] ++
 (List.finRange 28).map Event.horner ++ [.g]
def returned (st : State) : NKR_TermTail.Carrier :=
 (st.composition,st.openings.z,st.mask,st.g,st.h,st.copy.active)
end AspisR1.NLH_CompositionState
end
