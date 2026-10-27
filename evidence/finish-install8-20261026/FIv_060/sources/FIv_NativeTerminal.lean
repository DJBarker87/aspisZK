import FIv_TerminalParts
import FIv_PartsValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_NativeTerminal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)

theorem value (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array NQ 29#usize) 3#usize) (alpha : Array NQ 10#usize)
    (c : state_only_prefix.r0.Challenges) (out : NQ)
    (run : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 pub claims alpha c=ok (.Ok out))
    (hz : ∀ x∈c.zc.val,Canon x) (ha : ∀ x∈alpha.val,Canon x)
    (hm : Canon c.mu) (ht : Canon c.theta) :
    ∃ (selected : Array NQ 84#usize) (sem : FIv_TerminalTrace.SemPub)
      (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize) (g : NQ)
      (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1) (h : NQ),
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims=ok selected ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.semantic pub=ok sem ∧
      pool_v1.pair_forest_semantic_terminal.terminal_parts sem selected alpha
        c.lambda c.chi c.theta c.zc c.mu=ok (.Ok (out,c1,mask,g)) ∧
      ((∀ x∈semantic.val,Canon x) → (∀ x∈poseidon.val,Canon x) → Canon copy.residual →
        Canon h → Canon copy.active → Canon out ∧
        decode out=FIv_TerminalValue.formula (FIv_EqualityValue.weight c.zc alpha)
          (FIv_CompositionValue.polynomial (decode c.theta) semantic poseidon copy.residual)
          (decode c.mu) (decode h) (decode copy.active)) := by
  obtain ⟨selected,sem,c1,mask,g,gather,semanticCall,parts⟩ := FIv_TerminalParts.reached pub claims alpha c out run
  obtain ⟨semantic,poseidon,copy,h,computed⟩ := FIv_PartsValue.value sem selected alpha c.zc
    c.lambda c.chi c.theta c.mu out c1 mask g parts hz ha hm ht
  exact ⟨selected,sem,c1,mask,g,semantic,poseidon,copy,h,gather,semanticCall,parts,computed⟩
#print axioms value
end AspisR1.FIv_NativeTerminal
end
