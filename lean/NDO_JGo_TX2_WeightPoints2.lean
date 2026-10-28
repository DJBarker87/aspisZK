import NDO_JGo_TX2_WeightData
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints2
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step04 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=6#usize}⟩ successor04 carry04=
      ok (.cont (⟨{start:=0#usize,«end»:=5#usize}⟩,successor05,carry05)) := by
  with_unfolding_all rfl
#print axioms step04
theorem step05 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=5#usize}⟩ successor05 carry05=
      ok (.cont (⟨{start:=0#usize,«end»:=4#usize}⟩,successor06,carry06)) := by
  with_unfolding_all rfl
#print axioms step05
end AspisR1.JGo_TX2_WeightPoints2
end
