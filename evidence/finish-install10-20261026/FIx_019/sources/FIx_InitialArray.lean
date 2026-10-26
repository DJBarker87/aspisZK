import FIx_Builder
import FIv_PreparedMul
import FIq_Native10
import FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_InitialArray
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)
open FIv_PreparedNew (NP prepared)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev call := pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
abbrev callback := pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

theorem callback_value (fullRate full : NQ) (pRate pFull : NP) (o : Openings)
    (i : Usize) (result : NQ)
    (last : pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure)
    (hfr : Canon fullRate) (hf : Canon full)
    (hpr : ExtractedMaskPreparedState.PreparedFor (prepared pRate) (qm fullRate))
    (hpf : ExtractedMaskPreparedState.PreparedFor (prepared pFull) (qm full))
    (ho : ∀ x∈o.z.val,Canon x)
    (run : call (pRate,o,pFull) i=ok (result,last)) :
    Canon result ∧ decode result=(if i.val<8 then decode fullRate else decode full)*
      FIv_NativeArray.value o.z i.val ∧ last=(pRate,o,pFull) := by
  unfold call pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at run
  change (if i<poseidon2.RATE then do
    let q ← Array.index_usize o.z i
    let v ← field.PreparedQm31Multiplier.mul pRate q
    ok (v,(pRate,o,pFull))
    else do
    let q ← Array.index_usize o.z i
    let v ← field.PreparedQm31Multiplier.mul pFull q
    ok (v,(pRate,o,pFull)))=ok (result,last) at run
  by_cases hi : i<poseidon2.RATE
  · rw [if_pos hi] at run
    obtain ⟨cell,hcell,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨out,hout,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    have hc := FIv_NativeArray.canonical o.z i cell ho hcell
    have v := FIv_PreparedMul.value pRate fullRate cell out hfr hc hpr hout
    refine ⟨v.1,?_,rfl⟩
    have h8 : i.val<8 := by rw [poseidon2.RATE] at hi;scalar_tac
    rw [if_pos h8,v.2,←FIv_NativeArray.read o.z i cell hcell]
  · rw [if_neg hi] at run
    obtain ⟨cell,hcell,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨out,hout,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    have hc := FIv_NativeArray.canonical o.z i cell ho hcell
    have v := FIv_PreparedMul.value pFull full cell out hf hc hpf hout
    refine ⟨v.1,?_,rfl⟩
    have h8 : ¬i.val<8 := by rw [poseidon2.RATE] at hi;scalar_tac
    rw [if_neg h8,v.2,←FIv_NativeArray.read o.z i cell hcell]

theorem value (fullRate full : NQ) (pRate pFull : NP) (o : Openings)
    (out : Array NQ 16#usize) (hfr : Canon fullRate) (hf : Canon full)
    (hpr : ExtractedMaskPreparedState.PreparedFor (prepared pRate) (qm fullRate))
    (hpf : ExtractedMaskPreparedState.PreparedFor (prepared pFull) (qm full))
    (ho : ∀ x∈o.z.val,Canon x)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy callback
      field.QM31.ZERO (pRate,o,pFull)=ok out) :
    (∀ x∈out.val,Canon x) ∧ out.val.map decode=List.ofFn
      (fun i : Fin (16#usize).val=>(if i.val<8 then decode fullRate else decode full)*
        FIv_NativeArray.value o.z i.val) := by
  unfold array_from_fn_copy at run
  apply FIx_Builder.fromFn (16#usize) callback Canon decode (fun n=>(if n<8 then decode fullRate else decode full)*FIv_NativeArray.value o.z n) (pRate,o,pFull) out _ run
  intro i hi result last called
  exact callback_value fullRate full pRate pFull o i result last hfr hf hpr hpf ho called
#print axioms callback_value
#print axioms value
end AspisR1.FIx_InitialArray
end
