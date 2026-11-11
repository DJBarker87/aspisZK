import NDO_JFy_CompositionGathers
import NIH_AtPoint
import NHU_PoseidonSelectors
import NKG_OracleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermGatherPoseidon
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open pool_v1.pair_forest_semantic_terminal
abbrev Claims := Array NQ 84#usize
abbrev Point := Array NQ 10#usize
structure Packet (claims : Claims) (point : Point) where
 z : Array NQ 16#usize
 succ : Array NQ 16#usize
 xor12 : Array NQ 16#usize
 mask : Array NQ 10#usize
 selectors : pool_v1.pair_forest_copy_terminal.Selectors
 poseidonSelectors : state_only_poseidon.StateOnlyPoseidonSelectors
 poseidon : Array NQ 4#usize
 gather0 : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok z
 gather1 : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok succ
 gather2 : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok xor12
 gather3 : array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok mask
 selectorCall : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok selectors
 selectorHigh : canonical selectors.high
 selectorLow : canonical selectors.low
 poseidonSelectorCall : poseidon_selectors selectors=ok poseidonSelectors
 localSame : poseidonSelectors.local=selectors.low
 blockCanonical : Canon poseidonSelectors.block
 poseidonCall : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨z,succ,xor12⟩ poseidonSelectors=ok poseidon
 zCanonical : canonical z
 succCanonical : canonical succ
 xorCanonical : canonical xor12
 maskCanonical : canonical mask
 poseidonCanonical : canonical poseidon
/--237 actual gather/selector/308 chain. CLOSED308 is deterministic and is
consumed at the SAME generated openings and selector record; no oracle reply
or digest-value premise is present. This is source support pending218/261
and the complete237 native frame/call-order certificate. -/
theorem source (claims : Claims) (point : Point)
 (hc : canonical claims) (hp : canonical point) :
 ∃ p : Packet claims point,
 decoded p.poseidon=fun g=>R0P.poseidonPackingFormula
   ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
   (fun j=>R0P.poseidonScalarResidual (FJh_Native07RawValue.openings ⟨p.z,p.succ,p.xor12⟩)
     (decode p.poseidonSelectors.block) (decoded p.poseidonSelectors.local) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨z,succ,xor12,mask,⟨g0,hz⟩,⟨g1,hs⟩,⟨g2,hx⟩,⟨g3,hm⟩⟩ := JFy_CompositionGathers.source claims hc
 obtain ⟨selectors,sc,ch,cl,_⟩ := NIH_AtPoint.boxed point hp
 obtain ⟨ps,psc,ls,bc⟩ := NHU_PoseidonSelectors.result selectors ch
 have lc : canonical ps.local := by rw [ls];exact cl
 obtain ⟨poseidon,pc,cp,value⟩ := NKG_OracleSource.result ⟨z,succ,xor12⟩ ps hz hs hx lc bc
 let p : Packet claims point := ⟨z,succ,xor12,mask,selectors,ps,poseidon,g0,g1,g2,g3,sc,ch,cl,psc,ls,bc,pc,hz,hs,hx,hm,cp⟩
 exact ⟨p,value⟩
#print source
#print axioms source
end AspisR1.NKR_TermGatherPoseidon
end
