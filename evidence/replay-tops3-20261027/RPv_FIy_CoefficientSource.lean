import RPv_FIy_ValuePacked
import RPv_FIy_OccupancyPacked
import RPv_FIy_PublicDigest
import RPv_FIw_ScalarSuffix
import RPv_FIx_SchedulePacked
import RPv_FIx_PathPacked
set_option autoImplicit false
namespace AspisR1.FIy_CoefficientSource
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ScalarSuffix (Public Openings Selectors)

theorem factor (p : Public) (o : Openings) (s : Selectors) :
    pool_v1.pair_forest_semantic_terminal.semantic_packed p o s=(do
      let a ← pool_v1.pair_forest_semantic_terminal.add_schedule_lanes (Array.repeat 24#usize field.QM31.ZERO) p o s
      let b ← pool_v1.pair_forest_semantic_terminal.add_path_lanes a o s
      let c ← pool_v1.pair_forest_semantic_terminal.add_value_lanes b o s
      let d ← pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes c p o s
      let digest ← pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s
      let e ← pool_v1.pair_forest_semantic_terminal.add_preweighted d 84#usize digest
      FIw_ScalarSuffix.run p o s e) := by
  rfl
#print axioms factor
end AspisR1.FIy_CoefficientSource
