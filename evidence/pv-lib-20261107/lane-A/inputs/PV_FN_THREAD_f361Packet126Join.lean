import PV_FN_THREAD_f361Callee126
import PV_THR2_PacketField82Store
import PV_THR2_PacketScopeRead
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Packet126Join
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f361Callee126

def after126 {E : Type} (x : Input E) (p : Address) :=
  PV_FN_THREAD_f126.successOut (child x .packet ⟨x.a,17,[]⟩) ⟨x.a,17,[]⟩ p

def after84 {E : Type} (x : Input E) (p : Address) :=
  PV_THR2_Source361Chain82To84.after
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) (after126 x p)

/-- CLOSED126's full final store preserves each previously issued backing
cell outside the actual caller return slot. No126 body instruction is replayed. -/
theorem backing_frame {E : Type} (x : Input E) (p q : Address)
    (older : q.activation < x.s.nextActivation) (foreign : q.activation ≠ x.a) :
    (PV_FN_THREAD_f126_ReturnedStage.finalStore (child x .packet ⟨x.a,17,[]⟩)
      ⟨x.a,17,[]⟩ p).cells q = x.s.cells q := by
  let y := child x .packet (⟨x.a,17,[]⟩ : Address)
  have outside : q.activation ≠ y.a := Nat.ne_of_lt older
  have inner : q.activation ≠ y.s.nextActivation := by
    change q.activation ≠ x.s.nextActivation+1
    omega
  have native : q.activation ≠ y.s.nextActivation+1 := by
    change q.activation ≠ x.s.nextActivation+1+1
    omega
  have dest : q ≠ (⟨y.parent.activation,y.dest,[]⟩ : Address) := by
    intro h
    exact foreign (congrArg Address.activation h)
  have body := PV_FN_THREAD_f126_ReturnedStage.frame y ⟨x.a,17,[]⟩ p q
    outside inner native dest
  have args := PV_W1_ChildStoreFrame.arguments x.s.nextActivation
    [PV_STX2_TypedReferences.reference ⟨x.a,17,[]⟩ .null] 1
    {x.s with nextActivation := x.s.nextActivation+1} q (Nat.ne_of_lt older)
  exact body.trans args

/-- The Packet Option read at13726 is transported across126's complete store
and the existing source82..83 certificate. Its entry backing read is a local
constructor/clone-join obligation, not a new caller precondition. -/
theorem read13726 {E : Type} (x : Input E) (p : Address) (option : Data)
    (older : p.activation < x.s.nextActivation) (foreign : p.activation ≠ x.a)
    (payload : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s {p with fields := (p.fields ++ [2]) ++ [0]} = some option) :
    ∃ d, (after84 x p).current.status = .running d ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 84) d ∧
      PV_STX2_Store.read (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
        d.store (after84 x p).current.world d.frame.activation
        (.project (.local 28) .deref) = some option := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b
  let y := child x .packet (⟨x.a,17,[]⟩ : Address)
  let t := PV_FN_THREAD_f126_ReturnedStage.finalStore y ⟨x.a,17,[]⟩ p
  let packet := {p with fields := p.fields ++ [2]}
  let s := PV_THR2_Spawn361PacketField82Reached.prepared t x.a packet
  have referenceCell : t.cells ⟨x.a,29,[]⟩ =
      some (PV_STX2_TypedReferences.reference packet .null) := write_same _ _ _
  have next := PV_THR2_PacketField82Store.after x.C x.b t x.a x.parents x.loops
    packet x.w x.es x.stack referenceCell
  have shape : after84 x p =
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_THR2_F361.live.body.drop 84,loops := x.loops},x.parents,s⟩,x.w,x.es⟩,x.stack⟩ := next
  have field : s.cells ⟨x.a,28,[]⟩ =
      some (PV_STX2_TypedReferences.reference {packet with fields := packet.fields ++ [0]} .null) :=
    write_same _ _ _
  have preserved : s.cells {p with fields := []} = x.s.cells {p with fields := []} := by
    have different (i : Nat) : ({p with fields := []} : Address) ≠ ⟨x.a,i,[]⟩ := by
      intro h; exact foreign (congrArg Address.activation h)
    unfold s PV_THR2_Spawn361PacketField82Reached.prepared
    rw [write_other _ _ _ _ (different 28),write_other _ _ _ _ (different 30)]
    exact backing_frame x p {p with fields := []} older foreign
  rw [shape]
  refine ⟨_,rfl,⟨rfl,rfl,rfl,rfl⟩,?_⟩
  rw [PV_THR2_PacketScopeRead.read x.C x.b s x.w x.a packet field]
  change (s.cells {p with fields := []} >>= fun v => readFields B ((p.fields ++ [2]) ++ [0]) v) = _
  rw [preserved]
  exact payload

/-- Instantiate CLOSED126 at13323, then join its returned branch to the
actual13726 read. The discriminant here is opaque320's actual answer; there is
no assumed successful BODY126 reply. All other branches stay in the full Post. -/
theorem packet_join {E : Type} (x : Input E) (p : Address) (option : Data)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (callerOlder : x.a < x.s.nextActivation)
    (older : p.activation < x.s.nextActivation) (foreign : p.activation ≠ x.a)
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s ⟨x.a,17,[]⟩ = some (PV_FN_THREAD_f222_EntryOwned.root p))
    (payload : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s {p with fields := (p.fields ++ [2]) ++ [0]} = some option) :
    let y := child x .packet ⟨x.a,17,[]⟩
    PV_FN_THREAD_f126.Post y x.native ⟨x.a,17,[]⟩ p ∧
    (∀ old, (PV_FN_THREAD_f222.baseReply
      (PV_FN_THREAD_f126_ReturnedStage.childInput y ⟨x.a,17,[]⟩) x.native).answer =
        .returned (.ok old) →
      (∃ n, PV_THR2_IntrinsicState.advance
        (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.K
        (PV_FN_THREAD_f126_ReturnedStage.programs y)
        (PV_FN_THREAD_f126.installed y x.native ⟨x.a,17,[]⟩).H n
        (PV_FN_THREAD_f126_Arbitrary.entry y) = after84 x p) ∧
      ∃ d, (after84 x p).current.status = .running d ∧
        PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 84) d ∧
        PV_STX2_Store.read (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
          d.store (after84 x p).current.world d.frame.activation
          (.project (.local 28) .deref) = some option) := by
  dsimp only
  let y := child x .packet (⟨x.a,17,[]⟩ : Address)
  have contract := at_call x .packet ⟨x.a,17,[]⟩ p owner callerOlder root
  refine ⟨contract,?_⟩
  intro old answer
  have returned : PV_FN_THREAD_f126.Reached y x.native ⟨x.a,17,[]⟩
      (after126 x p) := by
    have returned := contract.2
    rw [answer] at returned
    exact returned.1
  obtain ⟨n,hn⟩ := returned.1
  change PV_THR2_IntrinsicState.advance
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.K
    (PV_FN_THREAD_f126_ReturnedStage.programs (child x .packet ⟨x.a,17,[]⟩))
    (PV_FN_THREAD_f126.installed (child x .packet ⟨x.a,17,[]⟩) x.native ⟨x.a,17,[]⟩).H n
    (PV_FN_THREAD_f126_Arbitrary.entry (child x .packet ⟨x.a,17,[]⟩)) = after126 x p at hn
  refine ⟨⟨n + PV_THR2_Source361Chain82To84.steps
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) (after126 x p),?_⟩,
    read13726 x p option older foreign payload⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,hn]
  exact PV_THR2_Source361Chain82To84.run _ _ _ _ _

#print axioms backing_frame
#print axioms read13726
#print axioms packet_join
end PV_FN_THREAD_f361Packet126Join
