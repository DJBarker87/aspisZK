import FIv_CompositionValue
import FIv_TerminalValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_PartsValue
open Aeneas Aeneas.Std Result
open FIv_TerminalTrace
open FIv_NativeValue (Canon decode K)

theorem value (pub : SemPub) (claims : Array NQ 84#usize)
    (point zc : Array NQ 10#usize) (lambda chi theta mu out : NQ)
    (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize) (g : NQ)
    (success : parts pub claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g)))
    (hl : ∀ x∈zc.val,Canon x) (hr : ∀ x∈point.val,Canon x) (hmu : Canon mu) (ht : Canon theta) :
    ∃ (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize)
      (copy : FIq_Native.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1) (h : NQ),
      ((∀ x∈semantic.val,Canon x) → (∀ x∈poseidon.val,Canon x) → Canon copy.residual →
        Canon h → Canon copy.active →
        Canon out ∧ decode out=FIv_TerminalValue.formula
          (FIv_EqualityValue.weight zc point)
          (FIv_CompositionValue.polynomial (decode theta) semantic poseidon copy.residual)
          (decode mu) (decode h) (decode copy.active)) := by
  obtain ⟨comp,h,active,called,⟨calls⟩⟩ := reached pub claims point zc lambda chi theta mu out c1 mask g success
  obtain ⟨semantic,poseidon,copy,ha,computed⟩ := FIv_CompositionValue.value
    pub claims point lambda chi theta comp g h active c1 mask called ht
  refine ⟨semantic,poseidon,copy,h,?_⟩
  intro hs hp hc hh hactive
  have cv := computed hs hp hc
  have arithmetic := FIv_TerminalValue.arithmetic zc point mu comp h active out calls hl hr hmu cv.1 hh
    (ha ▸ hactive)
  rw [cv.2,← ha] at arithmetic
  exact arithmetic
#print axioms value
end AspisR1.FIv_PartsValue
end
