import PV_LIB_SPEC_PrefixNative13
import PV_LIB_SPEC_ControlHistory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_PrefixHistory13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_ControlHistory (Invariant record_mono context_origin append_record)
/-- Recheck actual issued origins after installing callback stores and actual v2.
Scalar registers are source projections; native rsp/physical stack pairing is not proved here. The
unchanged origin/list lemmas are reused by name; no total byte image enters. -/
theorem step (cut : PV_LIB_SPEC_PrefixNative13.Cut) (values : PV_THR2_SourceStoreLibrary.Values PV_EVHB_OwnerMachine.OWNER Event) (p : Parameters) 
    (x : Execution) (valid : Invariant x) :
    Invariant (PV_LIB_SPEC_PrefixNative13.step cut values p x) := by
  unfold PV_LIB_SPEC_PrefixNative13.step
  cases native : PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none =>
    intro ctx member
    obtain ⟨args,source,mem,site,caller,req⟩ := valid ctx member
    exact ⟨args,source,record_mono _ _ _ _ mem,site,caller,req⟩
  | some pair =>
    obtain ⟨c,wait⟩ := pair
    simp only []
    cases origin : context x c wait with
    | none =>
      intro ctx member
      exact valid ctx member
    | some ctx =>
      simp only [origin]
      have association := context_origin x c wait ctx origin
      cases result : PV_LIB_SPEC_PrefixNative13.answer cut
          {p with resources := allocationResources p.environment ctx} c wait.request x.state.current.world with
      | none =>
        simp only [result]
        intro candidate member
        rcases List.mem_cons.mp member with rfl | member
        · exact association
        · exact valid candidate member
      | some reply =>
        simp only [result]
        exact append_record x _ ctx valid association

theorem initial (i : PV_LIB_SPEC_F0Full.Original) :
    Invariant (PV_LIB_SPEC_ResourceHistory.initial i) := by
  intro ctx member; cases member

theorem run (cut : PV_LIB_SPEC_PrefixNative13.Cut) (values : PV_THR2_SourceStoreLibrary.Values PV_EVHB_OwnerMachine.OWNER Event) (p : Parameters) 
    (n : Nat) (x : Execution) (valid : Invariant x) :
    Invariant (PV_LIB_SPEC_PrefixNative13.run cut values p n x) := by
  induction n generalizing x with
  | zero => exact valid
  | succ n ih => exact ih _ (step cut values p x valid)

/-- Source-history association for the new runtime is DERIVED at every
finite prefix. This establishes origin/operands, not native source adequacy
or correctness of a reservation model not installed in BoundRuntime. -/
theorem original (cut : PV_LIB_SPEC_PrefixNative13.Cut) (values : PV_THR2_SourceStoreLibrary.Values PV_EVHB_OwnerMachine.OWNER Event) (p : Parameters) 
    (i : PV_LIB_SPEC_F0Full.Original) (n : Nat) :
    Invariant (PV_LIB_SPEC_PrefixNative13.run cut values p n
      (PV_LIB_SPEC_ResourceHistory.initial i)) := run cut values p n _ (initial i)

#print axioms step
#print axioms initial
#print axioms run
#print axioms original
end PV_LIB_SPEC_PrefixHistory13
