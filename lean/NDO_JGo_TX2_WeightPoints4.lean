import NDO_JGo_TX2_WeightData
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints4
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step08 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=2#usize}⟩ successor08 carry08=
      ok (.cont (⟨{start:=0#usize,«end»:=1#usize}⟩,successor09,carry09)) := by
  with_unfolding_all rfl
#print axioms step08
theorem step09 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=1#usize}⟩ successor09 carry09=
      ok (.cont (⟨{start:=0#usize,«end»:=0#usize}⟩,successor10,carry10)) := by
  with_unfolding_all rfl
#print axioms step09
end AspisR1.JGo_TX2_WeightPoints4
end
