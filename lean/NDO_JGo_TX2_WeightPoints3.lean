import NDO_JGo_TX2_WeightData
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints3
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step06 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=4#usize}⟩ successor06 carry06=
      ok (.cont (⟨{start:=0#usize,«end»:=3#usize}⟩,successor07,carry07)) := by
  with_unfolding_all rfl
#print axioms step06
theorem step07 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=3#usize}⟩ successor07 carry07=
      ok (.cont (⟨{start:=0#usize,«end»:=2#usize}⟩,successor08,carry08)) := by
  with_unfolding_all rfl
#print axioms step07
end AspisR1.JGo_TX2_WeightPoints3
end
