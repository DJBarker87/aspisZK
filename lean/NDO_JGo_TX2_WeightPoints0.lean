import NDO_JGo_TX2_WeightData
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints0
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step00 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=10#usize}⟩ successor00 carry00=
      ok (.cont (⟨{start:=0#usize,«end»:=9#usize}⟩,successor01,carry01)) := by
  with_unfolding_all rfl
#print axioms step00
theorem step01 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=9#usize}⟩ successor01 carry01=
      ok (.cont (⟨{start:=0#usize,«end»:=8#usize}⟩,successor02,carry02)) := by
  with_unfolding_all rfl
#print axioms step01
end AspisR1.JGo_TX2_WeightPoints0
end
