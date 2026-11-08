import PV_FN_THREAD_f361Enter126
import PV_FN_THREAD_f361Packet126Join
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Calls126
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f361Callee126 PV_FN_THREAD_f361Enter126

def outcome {E : Type} (x : Input E) (c : Call) (arc p : Address) :=
  let y := child (moved x c) c arc
  match (PV_FN_THREAD_f222.baseReply
      (PV_FN_THREAD_f126_ReturnedStage.childInput y arc) x.native).answer with
  | .returned (.ok _) => PV_FN_THREAD_f126.successOut y arc p
  | _ => PV_FN_THREAD_f126_Other.after y x.native arc

/-- Moving the source argument preserves the independently established Arc
root except at the exact moved root. The concrete callers discharge this
separation by local indices (Packet17 versus30) or older activation (ScopeData). -/
theorem moved_root {E : Type} (x : Input E) (c : Call) (arc p : Address)
    (apart : ({arc with fields := []} : Address) ≠ ⟨x.a,argumentLocal c,[]⟩)
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s arc = some (PV_FN_THREAD_f222_EntryOwned.root p)) :
    readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (moved x c).s arc = some (PV_FN_THREAD_f222_EntryOwned.root p) := by
  unfold readAddress
  change ((write x.s ⟨x.a,argumentLocal c,[]⟩ none).cells
    {arc with fields := []} >>= fun v => readFields _ arc.fields v) = _
  rw [write_other _ _ _ _ apart]
  exact root

/-- At either actual source call, instantiate CLOSED126 and compose its
all-answer reached conclusion with the source call administration. No successful
BODY reply, reset store or new callee-contract hypothesis is introduced. -/
theorem source_join {E : Type} (x : Input E) (c : Call) (arc p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (older : arc.activation < x.s.nextActivation)
    (cell : x.s.cells ⟨x.a,argumentLocal c,[]⟩ =
      some (PV_STX2_TypedReferences.reference arc .null))
    (apart : ({arc with fields := []} : Address) ≠ ⟨x.a,argumentLocal c,[]⟩)
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s arc = some (PV_FN_THREAD_f222_EntryOwned.root p)) :
    let y := child (moved x c) c arc
    PV_FN_THREAD_f126.Post y x.native arc p ∧
    ∃ n, PV_THR2_IntrinsicState.advance
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.K
      (PV_FN_THREAD_f126_ReturnedStage.programs y)
      (PV_FN_THREAD_f126.installed y x.native arc).H n (before x c) =
      outcome x c arc p := by
  dsimp only
  let y := child (moved x c) c arc
  have post := at_call (moved x c) c arc p owner older (moved_root x c arc p apart root)
  change PV_FN_THREAD_f126.Post y x.native arc p at post
  have reached : PV_FN_THREAD_f126.Reached y x.native arc (outcome x c arc p) := by
    have cases := post.2
    change PV_FN_THREAD_f126.Reached y x.native arc
      (match (PV_FN_THREAD_f222.baseReply
        (PV_FN_THREAD_f126_ReturnedStage.childInput y arc) x.native).answer with
       | .returned (.ok _) => PV_FN_THREAD_f126.successOut y arc p
       | _ => PV_FN_THREAD_f126_Other.after y x.native arc)
    cases answer : (PV_FN_THREAD_f222.baseReply
      (PV_FN_THREAD_f126_ReturnedStage.childInput y arc) x.native).answer with
    | pending => simpa only [answer] using cases
    | fault f => simpa only [answer] using cases
    | returned result =>
      cases result with
      | fail err => simpa only [answer] using cases
      | div => simpa only [answer] using cases
      | ok v =>
        have success := cases
        rw [answer] at success
        exact success.1
  obtain ⟨n,hn⟩ := reached.1
  have entered := enter_call x c arc cell
  change PV_THR2_IntrinsicState.advance
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.K
    (PV_FN_THREAD_f126_ReturnedStage.programs y)
    (PV_FN_THREAD_f126.installed y x.native arc).H n
    (PV_FN_THREAD_f126_Arbitrary.entry y) = outcome x c arc p at hn
  refine ⟨post,⟨2+n,?_⟩⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,entered]
  exact hn

/--13323 separation is source-local17 versus moved-local30, derived here. -/
theorem packet {E : Type} (x : Input E) (p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (older : x.a < x.s.nextActivation)
    (cell : x.s.cells ⟨x.a,30,[]⟩ =
      some (PV_STX2_TypedReferences.reference ⟨x.a,17,[]⟩ .null))
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s ⟨x.a,17,[]⟩ = some (PV_FN_THREAD_f222_EntryOwned.root p)) :
    let y := child (moved x .packet) .packet ⟨x.a,17,[]⟩
    PV_FN_THREAD_f126.Post y x.native ⟨x.a,17,[]⟩ p ∧
    ∃ n, PV_THR2_IntrinsicState.advance
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.K
      (PV_FN_THREAD_f126_ReturnedStage.programs y)
      (PV_FN_THREAD_f126.installed y x.native ⟨x.a,17,[]⟩).H n (before x .packet) =
      outcome x .packet ⟨x.a,17,[]⟩ p := by
  exact source_join x .packet ⟨x.a,17,[]⟩ p owner older cell
    (by intro h; have indices := congrArg Address.localIndex h; cases indices) root

/--13522 borrows the ScopeData Arc stored INSIDE the Packet Option. The
root activation is the fresh Packet backing activation, not necessarily older
than f361. The constructor's issued/foreign-frame facts discharge separation. -/
theorem scope {E : Type} (x : Input E) (packetInner p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (older : packetInner.activation < x.s.nextActivation)
    (foreign : packetInner.activation ≠ x.a)
    (cell : x.s.cells ⟨x.a,35,[]⟩ =
      some (PV_STX2_TypedReferences.reference
        {packetInner with fields := ((packetInner.fields ++ [2]) ++ [0]) ++ [0]} .null))
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s {packetInner with fields := ((packetInner.fields ++ [2]) ++ [0]) ++ [0]} =
        some (PV_FN_THREAD_f222_EntryOwned.root p)) :
    let arc := {packetInner with fields := ((packetInner.fields ++ [2]) ++ [0]) ++ [0]}
    let y := child (moved x .scope) .scope arc
    PV_FN_THREAD_f126.Post y x.native arc p ∧
    ∃ n, PV_THR2_IntrinsicState.advance
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.K
      (PV_FN_THREAD_f126_ReturnedStage.programs y)
      (PV_FN_THREAD_f126.installed y x.native arc).H n (before x .scope) =
      outcome x .scope arc p := by
  dsimp only
  exact source_join x .scope _ p owner older cell
    (by intro h; exact foreign (congrArg Address.activation h)) root

#print axioms moved_root
#print axioms source_join
#print axioms packet
#print axioms scope
end PV_FN_THREAD_f361Calls126
