import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_CallbackCtor
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Constructor callbacks execute native argument/capture drops first. Their
actual drop associations, operator selection and runtime adequacy remain OPEN. -/

def callback_0 {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (c :
  aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure
  T0)
  (tupled_args :
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) (dropArgument : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 → P Unit) (dropCapture : aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure
  T0 → P Unit) : P aspis_prover.state_only_hiding.StateOnlyMaskBuildError := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout

theorem callback_0_fixed {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (c :
  aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure
  T0)
  (tupled_args :
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) (dropArgument : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 → P Unit) (dropCapture : aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure
  T0 → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_0 StateOnlyMaskNonceStoreInst c tupled_args dropArgument dropCapture) (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError.call_once StateOnlyMaskNonceStoreInst c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)))

#print axioms callback_0_fixed

def callback_1 (c :
  aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) (dropArgument : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 → P Unit) (dropCapture : aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure → P Unit) : P aspis_prover.state_only_hiding.StateOnlyMaskBuildError := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout

theorem callback_1_fixed (c :
  aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) (dropArgument : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 → P Unit) (dropCapture : aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_1 c tupled_args dropArgument dropCapture) (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError.call_once c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)))

#print axioms callback_1_fixed

def callback_2 (c : prover.derive_private_salts.closure)
  (tupled_args : alloc.collections.TryReserveError) (dropArgument : alloc.collections.TryReserveError → P Unit) (dropCapture : prover.derive_private_salts.closure → P Unit) : P verifier.Error := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure verifier.Error.Allocation

theorem callback_2_fixed (c : prover.derive_private_salts.closure)
  (tupled_args : alloc.collections.TryReserveError) (dropArgument : alloc.collections.TryReserveError → P Unit) (dropCapture : prover.derive_private_salts.closure → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_2 c tupled_args dropArgument dropCapture) (prover.derive_private_salts.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Allocation) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Allocation) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok verifier.Error.Allocation)))

#print axioms callback_2_fixed

def callback_4 (c : prover.prepare_opening.closure) (tupled_args : aspis_core.r0.Error) (dropArgument : aspis_core.r0.Error → P Unit) (dropCapture : prover.prepare_opening.closure → P Unit) : P verifier.Error := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure verifier.Error.Allocation

theorem callback_4_fixed (c : prover.prepare_opening.closure) (tupled_args : aspis_core.r0.Error) (dropArgument : aspis_core.r0.Error → P Unit) (dropCapture : prover.prepare_opening.closure → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_4 c tupled_args dropArgument dropCapture) (prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Allocation) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Allocation) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok verifier.Error.Allocation)))

#print axioms callback_4_fixed

def callback_5 (c : prover.publish_compact.closure) (tupled_args : compact.CodecError) (dropArgument : compact.CodecError → P Unit) (dropCapture : prover.publish_compact.closure → P Unit) : P verifier.Error := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure verifier.Error.Semantic

theorem callback_5_fixed (c : prover.publish_compact.closure) (tupled_args : compact.CodecError) (dropArgument : compact.CodecError → P Unit) (dropCapture : prover.publish_compact.closure → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_5 c tupled_args dropArgument dropCapture) (prover.publish_compact.closure.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError.call_once c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Semantic) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Semantic) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok verifier.Error.Semantic)))

#print axioms callback_5_fixed

def callback_6 (c : prover.publish_compact.closure_1) (tupled_args : compact.CodecError) (dropArgument : compact.CodecError → P Unit) (dropCapture : prover.publish_compact.closure_1 → P Unit) : P verifier.Error := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure verifier.Error.Semantic

theorem callback_6_fixed (c : prover.publish_compact.closure_1) (tupled_args : compact.CodecError) (dropArgument : compact.CodecError → P Unit) (dropCapture : prover.publish_compact.closure_1 → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_6 c tupled_args dropArgument dropCapture) (prover.publish_compact.closure_1.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError.call_once c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Semantic) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Semantic) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok verifier.Error.Semantic)))

#print axioms callback_6_fixed

def callback_7 (c : prover.derive_private_salt_step.closure)
  (tupled_args : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (dropArgument : aspis_prover.state_only_hiding.StateOnlyMaskBuildError → P Unit) (dropCapture : prover.derive_private_salt_step.closure → P Unit) : P verifier.Error := do
  let _ ← dropArgument tupled_args
  let _ ← dropCapture c
  pure verifier.Error.Semantic

theorem callback_7_fixed (c : prover.derive_private_salt_step.closure)
  (tupled_args : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (dropArgument : aspis_prover.state_only_hiding.StateOnlyMaskBuildError → P Unit) (dropCapture : prover.derive_private_salt_step.closure → P Unit)
    (ha : FinishedView (dropArgument tupled_args) (.ok ()))
    (hc : FinishedView (dropCapture c) (.ok ())) :
    FinishedView (callback_7 c tupled_args dropArgument dropCapture) (prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError.call_once c tupled_args) := by
  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Semantic) ha
    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok verifier.Error.Semantic) hc
      (fun _ => PV_EVH_Prefix.lift_fixed (.ok verifier.Error.Semantic)))

#print axioms callback_7_fixed
end PV_EVH_CallbackCtor
