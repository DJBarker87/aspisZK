import NDO_JGo_TX2_WeightData
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints1
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step02 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=8#usize}⟩ successor02 carry02=
      ok (.cont (⟨{start:=0#usize,«end»:=7#usize}⟩,successor03,carry03)) := by
  with_unfolding_all rfl
#print axioms step02
theorem step03 : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{start:=0#usize,«end»:=7#usize}⟩ successor03 carry03=
      ok (.cont (⟨{start:=0#usize,«end»:=6#usize}⟩,successor04,carry04)) := by
  with_unfolding_all rfl
#print axioms step03
end AspisR1.JGo_TX2_WeightPoints1
end
