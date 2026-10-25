import Tx1Q_Accepted
import Op4P_Audit
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Nonvacuity
open AspisR1CurrentCaller Tx1Q_Carriers

theorem extraction_satisfiable {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ native1 native2, S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps {adapterOps with op43 := S2W_DigestExtraction.digest hashv}
        (Tx1Q_SameCut.dictionary ops reserved query geo) B std) native1 native2 hashv :=
  Op4P_Audit.extraction_satisfiable adapterOps (Tx1Q_Execution.base ops reserved query geo) B std hashv

/-- Local prefix witness only: the concrete constructor and pending allocator
can both succeed. This is not a joint native/crypto accepted-pair fixture. -/
theorem initial_pending : ∃ (a : C.A) (b : C.B),
    Tx1Q_PrefixInstall.initial true .S2 = ok (.Ok a) ∧
    Tx1Q_PrefixInstall.newPending true a.weights.deref = ok (.Ok b) := by
  let weights : alloc.vec.Vec S.K :=
    ⟨List.replicate 64 Port2_Initial.zeroK,by simp; scalar_tac⟩
  let a := unAccumulator (Port2_Initial.initial weights)
  have init : Tx1Q_PrefixInstall.initial true .S2 = ok (.Ok a) := by
    simp only [Tx1Q_PrefixInstall.initial,variant,Port3_Initial.constructor_shell,
      CheckpointBytes3Allocation.filled_exact,if_true,Port2_Initial.newS2,bind_tc_ok,
      Tx1Q_PrefixInstall.topResult]
    rfl
  have size : (slice k a.weights.deref).val.length = 64 := by
    change ((List.replicate 64 Port2_Initial.zeroK).map unK |>.map k).length = 64
    simp only [List.length_map,List.length_replicate]
  let state : S.B := ⟨Port3_PendingInstall.raw (slice k a.weights.deref),0#usize⟩
  refine ⟨a,unPending state,init,?_⟩
  unfold Tx1Q_PrefixInstall.newPending Port3_NativePendingInstall.source
  rw [Port3_NativePendingInstall.emitted_exact true _ size]
  rfl

#print axioms extraction_satisfiable
#print axioms initial_pending
end AspisR1.Tx1Q_Nonvacuity
end
