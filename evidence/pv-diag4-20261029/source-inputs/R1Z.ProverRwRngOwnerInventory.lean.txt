import R1Z.ProverRwRngOwnerState
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerInventory
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerInduction ProverRwRngOwnerEvents
open ProverRwRngOwnerDraw ProverRwRngOwnerState
variable [ErasureFns]
abbrev Reply := ProverRwRngTape.Reply
abbrev Event := Array U8 64#usize × Nat × Option Reply

def drawCount : List State → Nat
  | [] => 0
  | s :: states => (if s.2 < 16#usize then 1 else 0) + drawCount states

def events : List State → List Event
  | [] => []
  | s :: states =>
    if s.2 < 16#usize then
      (Array.repeat 64#usize 0#u8,s.1.used.val,s.1.replies.val[s.1.used.val]?) :: events states
    else events states

theorem body_event (nonce : Array U8 32#usize) (p : Tape) (retry : Usize)
    (below : retry < 16#usize) (flow : ControlFlow State (Tape × Status))
    (step : newBody nonce (p,retry) = .ok flow) :
    ∃ reply, Tape.Insts.Prover_rw_rng_preflightDraw64.fill p (Array.repeat 64#usize 0#u8) = .ok reply ∧
      afterFill nonce retry reply = .ok flow ∧
      p.replies.val[p.used.val]? = some (reply.2,reply.1.2) := by
  rw [draw_factor,if_pos below] at step
  cases draw : Tape.Insts.Prover_rw_rng_preflightDraw64.fill p (Array.repeat 64#usize 0#u8) with
  | fail e => rw [draw] at step; cases step
  | div => rw [draw] at step; cases step
  | ok reply =>
    rw [draw] at step
    exact ⟨reply,rfl,step,(fill_event p _ reply draw).2.2⟩

theorem replay_inventory (nonce : Array U8 32#usize) {s : State} {states : List State}
    {result : Tape × Status} (run : Replay (newBody nonce) s states result) :
    result.1.replies = s.1.replies ∧
    result.1.used.val = s.1.used.val + drawCount states ∧
    drawCount states ≤ 16 - s.2.val := by
  induction run with
  | @finish s result step =>
    rcases s with ⟨p,retry⟩
    have inventory := body_state nonce p retry (.done result) step
    by_cases below : retry < 16#usize
    · simp only [below,if_true,providerOf] at inventory
      simp only [drawCount,below,if_true,List.nil_eq,zero_add,add_zero]
      refine ⟨inventory.1,inventory.2,?_⟩
      have belowNat : retry.val < 16 := below
      omega
    · simp only [below,if_false,providerOf] at inventory
      simp only [drawCount,below,if_false,zero_add,add_zero]
      exact ⟨congrArg Tape.replies inventory,congrArg (fun p : Tape => p.used.val) inventory,Nat.zero_le _⟩
  | @next s after states result step rest ih =>
    rcases s with ⟨p,retry⟩
    obtain ⟨below,increased⟩ := body_progress nonce p retry after step
    have inventory := body_state nonce p retry (.cont after) step
    simp only [below,if_true,providerOf] at inventory
    simp only [drawCount,below,if_true]
    refine ⟨ih.1.trans inventory.1,?_,?_⟩
    · omega
    · have belowNat : retry.val < 16 := below
      omega

/-- The emitted primitive receives a fresh zero buffer at every active body.
The trace carries the entire ordered 64-byte reply and error tag, not a hash
or success-only projection. Index availability is proved separately below. -/
theorem replay_events (nonce : Array U8 32#usize) {s : State} {states : List State}
    {result : Tape × Status} (run : Replay (newBody nonce) s states result) :
    events states = (List.range' s.1.used.val (drawCount states)).map
      (fun index => (Array.repeat 64#usize 0#u8,index,s.1.replies.val[index]?)) := by
  induction run with
  | @finish s result step =>
    rcases s with ⟨p,retry⟩
    by_cases below : retry < 16#usize
    · simp only [events,drawCount,below,if_true,add_zero]
      rfl
    · simp only [events,drawCount,below,if_false,zero_add,List.range'_zero,List.map_nil]
  | @next s after states result step rest ih =>
    rcases s with ⟨p,retry⟩
    obtain ⟨below,increased⟩ := body_progress nonce p retry after step
    have inventory := body_state nonce p retry (.cont after) step
    simp only [below,if_true,providerOf] at inventory
    simp only [events,drawCount,below,if_true,ih,inventory.1,inventory.2]
    rw [Nat.add_comm 1,List.range'_succ]
    rfl

theorem replay_available (nonce : Array U8 32#usize) {s : State} {states : List State}
    {result : Tape × Status} (run : Replay (newBody nonce) s states result) :
    ∀ event ∈ events states, event.2.2.isSome = true := by
  induction run with
  | @finish s result step =>
    rcases s with ⟨p,retry⟩
    by_cases below : retry < 16#usize
    · obtain ⟨reply,draw,tail,available⟩ := body_event nonce p retry below (.done result) step
      simp only [events,below,if_true,available,List.mem_cons,List.not_mem_nil,or_false]
      intro event he
      subst event
      rfl
    · simp only [events,below,if_false,List.not_mem_nil,false_implies,implies_true]
  | @next s after states result step rest ih =>
    rcases s with ⟨p,retry⟩
    obtain ⟨below,increased⟩ := body_progress nonce p retry after step
    obtain ⟨reply,draw,tail,available⟩ := body_event nonce p retry below (.cont after) step
    simp only [events,below,if_true,available,List.mem_cons]
    intro event he
    rcases he with head | tail
    · subst event; rfl
    · exact ih event tail

#print axioms body_event
#print axioms replay_inventory
#print axioms replay_events
#print axioms replay_available
end R1Z.ProverRwRngOwnerInventory
