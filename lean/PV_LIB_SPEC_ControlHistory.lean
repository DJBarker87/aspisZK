import PV_LIB_SPEC_ControlRuntime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ControlHistory
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_NativeRuntime PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
local instance : DecidableEq Site := Classical.decEq Site
local instance : DecidableEq (PV_STX2_Native.Request Data) := Classical.decEq _

def Invariant (x : Execution) : Prop :=
  ∀ ctx ∈ x.consumed,
    ctx.arguments = arguments ctx.request ∧
    ∃ origin ∈ x.issued,
      origin.site = ctx.site ∧ origin.caller = ctx.caller ∧ origin.request = ctx.request

theorem record_mono (before after : State) (old : List Issued) :
    ∀ origin ∈ old, origin ∈ PV_LIB_SPEC_ControlRuntime.recordIssue before after old := by
  intro origin member
  unfold PV_LIB_SPEC_ControlRuntime.recordIssue
  cases PV_LIB_SPEC_ControlRuntime.issuing before with
  | none => exact member
  | some issued =>
    obtain ⟨site,caller⟩ := issued
    cases after.current.status with
    | running c =>
      cases hw : c.frame.waiting with
      | none => simpa only [hw] using member
      | some wait => simpa only [hw] using (List.mem_cons_of_mem (⟨site,caller,wait.request⟩ : Issued) member)
    | returned result store => exact member
    | fault f store => exact member
    | undefined site store => exact member

theorem context_origin (x : Execution) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (found : context x c wait = some ctx) :
    ctx.arguments = arguments ctx.request ∧
    ∃ origin ∈ x.issued,
      origin.site = ctx.site ∧ origin.caller = ctx.caller ∧ origin.request = ctx.request := by
  unfold context at found
  cases selected : x.issued.find? (fun (issued : Issued) => decide
    (issued.caller = c.frame.activation ∧ issued.request = wait.request)) with
  | none => simp only [selected] at found; cases found
  | some origin =>
    simp only [selected,Option.pure_def] at found
    cases found
    have member := List.mem_of_find?_eq_some selected
    have matched := List.find?_some selected
    have equal : origin.caller = c.frame.activation ∧ origin.request = wait.request :=
      of_decide_eq_true matched
    exact ⟨rfl,origin,member,rfl,equal.1,equal.2⟩

theorem append_record (x : Execution) (out : State) (ctx : Context)
    (valid : Invariant x)
    (origin : ctx.arguments = arguments ctx.request ∧
      ∃ source ∈ x.issued, source.site = ctx.site ∧ source.caller = ctx.caller ∧ source.request = ctx.request) :
    Invariant ⟨out,PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,ctx :: x.consumed⟩ := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨args,source,mem,site,caller,req⟩ := origin
    exact ⟨args,source,record_mono _ _ _ _ mem,site,caller,req⟩
  · obtain ⟨args,source,mem,site,caller,req⟩ := valid candidate member
    exact ⟨args,source,record_mono _ _ _ _ mem,site,caller,req⟩

theorem step (table : FullStoreActionTable) (p : Parameters) (abi : ABI)
    (x : Execution) (valid : Invariant x) :
    Invariant (PV_LIB_SPEC_ControlRuntime.step table p abi x) := by
  unfold PV_LIB_SPEC_ControlRuntime.step
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
      cases result : PV_LIB_SPEC_BoundRuntime.answer
          {p with resources := allocationResources p.environment ctx} abi c wait.request x.state.current.world with
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

theorem run (table : FullStoreActionTable) (p : Parameters) (abi : ABI)
    (n : Nat) (x : Execution) (valid : Invariant x) :
    Invariant (PV_LIB_SPEC_ControlRuntime.run table p abi n x) := by
  induction n generalizing x with
  | zero => exact valid
  | succ n ih => exact ih _ (step table p abi x valid)

/-- Source-history association for the new runtime is DERIVED at every
finite prefix. This establishes origin/operands, not native source adequacy
or correctness of a reservation model not installed in BoundRuntime. -/
theorem original (table : FullStoreActionTable) (p : Parameters) (abi : ABI)
    (i : PV_LIB_SPEC_F0Full.Original) (n : Nat) :
    Invariant (PV_LIB_SPEC_ControlRuntime.run table p abi n
      (PV_LIB_SPEC_ResourceHistory.initial i)) := run table p abi n _ (initial i)

#print axioms Invariant
#print axioms record_mono
#print axioms context_origin
#print axioms append_record
#print axioms step
#print axioms initial
#print axioms run
#print axioms original
end PV_LIB_SPEC_ControlHistory
