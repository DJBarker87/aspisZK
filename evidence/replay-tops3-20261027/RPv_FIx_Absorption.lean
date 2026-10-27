import RPv_FIx_Builder
import RPv_FIx_HighSumInner
import R0P.Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_Absorption
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev call := pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
abbrev callback := pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

def blocks (fixed two eight nodes : K) (i : Nat) : K :=
  if i<2 then fixed else if i<8 then fixed+two else ((fixed+two)+eight)+nodes

def blockRun (fixed two eight nodes : NQ) (i : Usize) : Result NQ :=
  if i<2#usize then ok fixed else if i<poseidon2.RATE then field.QM31.add fixed two
  else do
    let a ← field.QM31.add fixed two
    let b ← field.QM31.add a eight
    field.QM31.add b nodes

theorem block_value (fixed two eight nodes result : NQ) (i : Usize)
    (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
    (run : blockRun fixed two eight nodes i=ok result) :
    Canon result ∧ decode result=blocks (decode fixed) (decode two) (decode eight) (decode nodes) i.val := by
  unfold blockRun at run
  by_cases h2 : i<2#usize
  · rw [if_pos h2] at run
    cases Result.ok.inj run
    exact ⟨hf,by simp only [blocks,if_pos (show i.val<2 by scalar_tac)]⟩
  · rw [if_neg h2] at run
    have hn2 : ¬i.val<2 := by scalar_tac
    by_cases h8 : i<poseidon2.RATE
    · rw [if_pos h8] at run
      have v := FIv_NativeValue.add fixed two result hf ht run
      refine ⟨v.1,?_⟩
      rw [v.2,blocks,if_neg hn2,if_pos (show i.val<8 by rw [poseidon2.RATE] at h8; scalar_tac)]
    · rw [if_neg h8] at run
      have hn8 : ¬i.val<8 := by rw [poseidon2.RATE] at h8; scalar_tac
      obtain ⟨a,ha,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨b,hb,run⟩ := FIv_Map.bind_success _ _ _ run
      have va := FIv_NativeValue.add fixed two a hf ht ha
      have vb := FIv_NativeValue.add a eight b va.1 he hb
      have vc := FIv_NativeValue.add b nodes result vb.1 hn run
      exact ⟨vc.1,by rw [vc.2,vb.2,va.2,blocks,if_neg hn2,if_neg hn8]⟩

theorem callback_value (low fixed two eight nodes : NQ) (o : Array NQ 16#usize)
    (i : Usize) (result : NQ)
    (last : pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure)
    (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
    (ho : ∀ x∈o.val,Canon x)
    (run : call (fixed,two,eight,nodes,low,o) i=ok (result,last)) :
    Canon result ∧ decode result=decode low*blocks (decode fixed) (decode two) (decode eight)
      (decode nodes) i.val*FIv_NativeArray.value o i.val ∧ last=(fixed,two,eight,nodes,low,o) := by
  unfold call pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at run
  obtain ⟨b,hb,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨weighted,hw,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨cell,hc,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨out,hout,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
  have vb := block_value fixed two eight nodes b i hf ht he hn hb
  have vw := FIv_NativeValue.mul low b weighted hl vb.1 hw
  have vc := FIv_NativeArray.canonical o i cell ho hc
  have vo := FIv_NativeValue.mul weighted cell out vw.1 vc hout
  refine ⟨vo.1,?_,rfl⟩
  rw [vo.2,vw.2,vb.2,←FIv_NativeArray.read o i cell hc]

#print axioms block_value
#print axioms callback_value
end AspisR1.FIx_Absorption
end
