import PV_LIB_Arc124
import PV_FN_THREAD_f361OwnEntry124Pre
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Caller124
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f361 PV_FN_THREAD_f361OwnEntry
open PV_FN_THREAD_f361JoinStatements PV_FN_THREAD_f361OwnEntry124Pre
/-- Discharge the literal CLOSED124 Pre from the caller's existing local
Context, including its lower/suspended-frame bounds. No new count, alias,
success or caller-global invariant is introduced. -/
theorem provider_pre (x : Input) (pre : Pre x) (s : Store Data) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (payload : Data)
    (context : Context x (state x s (x.parent :: x.parents) []
      (PV_THR2_F361.live.body.drop 58) w es x.stack)) :
    PV_FN_THREAD_f124.Pre (input124 x (call x s payload) w es) :=
  PV_FN_THREAD_f361OwnEntry124Pre.provider_pre x pre s w es payload context.1 context.2.1

/-- The library graph uses the SAME provider input and the actual caller's
resource environment. This is a local join adapter; the caller still supplies
its selected cut, not a fabricated whole-run invariant. -/
theorem installed (x : Input) (pre : Pre x) (s : Store Data) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (payload : Data)
    (context : Context x (state x s (x.parent :: x.parents) []
      (PV_THR2_F361.live.body.drop 58) w es x.stack)) :
    ∃ out, PV_FN_THREAD_f124.Reached (input124 x (call x s payload) w es)
      x.native x.resources x.encode x.arcShape out ∧
      PV_LIB_Arc124.law (input124 x (call x s payload) w es)
        x.native x.resources x.encode x.arcShape (PV_LIB.observe out) :=
  PV_LIB_Arc124.installed _ _ _ _ _ (provider_pre x pre s w es payload context)

/-- Instantiate the count laws at an ACTUAL reached caller entry. Named
atomic semantics is obtained from the caller's existing DocumentedFacts,
not assumed separately at each AtomicUsize::new request. -/
theorem counts (x : Input) (pre : Pre x) (facts : DocumentedFacts x)
    (s : Store Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (payload sv wv : Data)
    (heap : Nat)
    (context : Context x (state x s (x.parent :: x.parents) []
      (PV_THR2_F361.live.body.drop 58) w es x.stack))
    (q : State) (run : Execution x (entry x) q)
    (atCall : AtCall x q (call x s payload)) (world : q.current.world = w)
    (events : q.current.events = es)
    (function : PV_THR2_OffPath.functionId (call x s payload).callee = some 124)
    (sa : (PV_FN_THREAD_f124_BoxContract.strong (input124 x (call x s payload) w es)
      x.native).answer = .returned (.ok sv))
    (wa : (PV_FN_THREAD_f124_BoxContract.weak (input124 x (call x s payload) w es)
      x.native).answer = .returned (.ok wv))
    (post : PV_FN_THREAD_f124.Successful (input124 x (call x s payload) w es)
      x.native x.resources x.encode x.arcShape sv wv heap) :
    let y := input124 x (call x s payload) w es
    let B := PV_THR2_OwnInitExactReturnedCases.carrier y.C y.b
    let t := PV_FN_THREAD_f124_ReturnedPost.store y sv wv
    let p := PV_FN_THREAD_f124_StorePost.backing y sv wv
    readAddress B t (PV_THR2_LibrarySemantics_ArcClone.countAddress p) = some (.number 1) ∧
    readAddress B t {p with fields := p.fields ++ [1,0,0]} = some (.number 1) := by
  have documented := facts.atomicNew q (call x s payload) run atCall function
  rw [world,events] at documented
  exact PV_FN_THREAD_f361Provider124Counts.returned_counts _ _ _ _ _ sv wv heap
    (provider_pre x pre s w es payload context) documented sa wa post
#print axioms provider_pre
#print axioms installed
#print axioms counts
end PV_LIB_A_Caller124
