import NBN_FirstByteDependency
import NBN_AccountCallbackObstruction
set_option autoImplicit false
noncomputable section
namespace NBN_U04
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem conditional_helpers (enc : NBN_DigestResultDependency.Encode)
    (NBN_Dep_DigestEncodeRaw : NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw enc) :
    (∀ d, NBN_FirstByteDependency.first enc d = pool_v1.pair_forest_accounts.first_canonical_byte d) ∧
    (∀ d, NBN_FirstByteDependency.lane enc d = pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d) :=
  ⟨NBN_FirstByteDependency.first_source enc NBN_Dep_DigestEncodeRaw,
    NBN_FirstByteDependency.lane_source enc (fun d _ => NBN_Dep_DigestEncodeRaw d)⟩

#print axioms conditional_helpers
end NBN_U04
