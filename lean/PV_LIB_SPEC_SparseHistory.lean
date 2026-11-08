import PV_LIB_SPEC_SparseRuntime
import PV_LIB_SPEC_ControlHistory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SparseHistory
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_ControlHistory (Invariant record_mono context_origin append_record)
/-- Recheck the actual-history invariant against the sparse runtime. The
unchanged origin/list lemmas are reused by name; no total byte image enters. -/
theorem step (table : FullStoreActionTable) (p : Parameters) 
    (x : Execution) (valid : Invariant x) :
    Invariant (PV_LIB_SPEC_SparseRuntime.step table p x) := by
  unfold PV_LIB_SPEC_SparseRuntime.step
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
      cases result : PV_LIB_SPEC_SparseRuntime.answer
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

theorem run (table : FullStoreActionTable) (p : Parameters) 
    (n : Nat) (x : Execution) (valid : Invariant x) :
    Invariant (PV_LIB_SPEC_SparseRuntime.run table p n x) := by
  induction n generalizing x with
  | zero => exact valid
  | succ n ih => exact ih _ (step table p x valid)

/-- Source-history association for the new runtime is DERIVED at every
finite prefix. This establishes origin/operands, not native source adequacy
or correctness of a reservation model not installed in BoundRuntime. -/
theorem original (table : FullStoreActionTable) (p : Parameters) 
    (i : PV_LIB_SPEC_F0Full.Original) (n : Nat) :
    Invariant (PV_LIB_SPEC_SparseRuntime.run table p n
      (PV_LIB_SPEC_ResourceHistory.initial i)) := run table p n _ (initial i)

#print axioms step
#print axioms initial
#print axioms run
#print axioms original
end PV_LIB_SPEC_SparseHistory
