import R1Z.PV_Join_Wire_Op82
import R1Z.PV_Join_Wire_Op83
import R1Z.PV_Join_Wire_Op86
import R1Z.PV_Join_Wire_Op111
import R1Z.PV_Join_Wire_Op114
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry82
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op82Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.U8 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp82.aspis_core.r0.merkle.C1_TAG
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op82 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op82.op82_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry82
end
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry83
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op83Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.U8 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp83.aspis_core.r0.merkle.C2_TAG
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op83 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op83.op83_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry83
end
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry86
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op86Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.Usize :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp86.aspis_core.r0.opening.LANES
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op86 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op86.op86_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry86
end
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry111
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op111Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.U64 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp111.aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op111 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op111.op111_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry111
end
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry114
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op114Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.state_only_hiding.StateOnlyHidingContext →
        aspis_core.state_only_hiding.StateOnlyHidingContext → Result Bool :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun a b => PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq a b
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op114 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext a b
  exact R1Z.PV_Join_Wire_Op114.op114_source base ops a b
#print axioms equation
end R1Z.PV_Join_Wire_Entry114
end
