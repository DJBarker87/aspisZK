import LIBC_ResultGraph
import LIBC_VStateCarriers
import NJZ_Weights
set_option autoImplicit false
noncomputable section
namespace LIBC_WeightsNew
open Aeneas Aeneas.Std Result AspisR1 RSL
def Domain (a : LIB_VCarriers.Acc) : Prop :=
 a.weights.val.length=64 ∧ ∀ q ∈ a.weights.val, Port3_FlushInstall.Canonical (LIBC_VStateCarriers.q q)
def port : core.result.Result LIB_VCarriers.Weights VTop_Stages.verifier.Error →
 Except LIB_VCarriers.VErr LIB_VCarriers.Weights
 | .Ok b => .ok b | .Err e => .error e
def model (a : LIB_VCarriers.Acc) (env : Env) :=
 Port3_PendingInstall.pending env.reservation (LIBC_VStateCarriers.toAcc a).weights.deref
def child : Child LIB_VCarriers.Acc (Except LIB_VCarriers.VErr LIB_VCarriers.Weights) :=
 ⟨Domain,fun a => LIB_Carriers.resultGraph port (model a) (fun _ => [])⟩
def value (a : LIB_VCarriers.Acc) (env : Env) :=
 LIBC_ResultGraph.value port (.error .Allocation) (model a env)
theorem returns (a : LIB_VCarriers.Acc) (env : Env) :
 NND_Returned.Returns (child.law a) env (value a env) := LIBC_ResultGraph.returns _ _ _ _ env
theorem functional : Child.Functional child := by
 intro a _
 exact LIBC_ResultGraph.functional _ _ _
/-- Full source occurrence with its original arbitrary Reservation. Binding
its discarded error payload to Env's Bool is the existing rev3 runtime item;
this equation preserves BOTH reservation outcomes. -/
theorem source (a : LIB_VCarriers.Acc) (env : Env) (r : NP6_StdModel.Reservation)
 (binding : NJC_FilledClause.reserved r = env.reservation) (domain : Domain a) :
 Port3_QueryInstall.result
  (Port3_NativePendingBody.extracted (NJR_ReservationRaw.filled r)
   (LIBC_VStateCarriers.toAcc a).weights.deref) = model a env := by
 rw [NJR_ReservationRaw.pending]
 change Port3_NativePendingInstall.source (NJC_FilledClause.reserved r)
  (LIBC_VStateCarriers.toAcc a).weights.deref = _
 rw [Port3_NativePendingInstall.reference_eq _ _ (by
  change (LIBC_VStateCarriers.toAcc a).weights.val.length=64
  rw [LIBC_VStateCarriers.weights_length]
  exact domain.1),binding]
 rfl
theorem native_arguments (a : LIB_VCarriers.Acc) :
 (LIBC_VStateCarriers.toAcc a).weights.deref.val = a.weights.val.map LIBC_VStateCarriers.q := rfl
theorem graph (a : LIB_VCarriers.Acc) (env : Env)
 (o : Obs (Except LIB_VCarriers.VErr LIB_VCarriers.Weights)) :
 child.law a env o ↔ o = LIB_Carriers.resultObs port [] (model a env) := Iff.rfl
#print axioms returns
#print axioms functional
#print axioms source
#print axioms native_arguments
#print axioms graph
end LIBC_WeightsNew
