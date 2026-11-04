import Lean
import NFY_Part028
import KMX_CopyMeaning
import NFY_Part027

-- BEGIN copied NEE_ValidatorOracle: evidence/slice-s-compose2-20261029/NEE_ValidatorOracle.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ValidatorOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_ValidatorTrace
attribute [local instance] Classical.propDecidable
def tail (pay : Statement → Result (core.result.Result (Array U8 216#usize) PaymentError))
    (lane : Array U32 8#usize → Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1))
    (late : NFY_NBN_LateSummary.Statement → Slice U8 → Result (core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 × Slice U8)) (s : Statement) : R × List Call :=
  let d := (parts s).2.2.2.2.1
  match lane d with
  | .fail e => (.fail e,[.lane d])
  | .div => (.div,[.lane d])
  | .ok (.Err e) => (ok (.Err (.Account e)),[.lane d])
  | .ok (.Ok l) =>
    if l ≠ (common s).output_lane then (ok (.Err .OutputLaneMismatch),[.lane d])
    else
      let arg := (common s).lane_transition
      let out := NFY_NBN_LateResult.zero
      let r : R := do
        let (status,_) ← late arg out
        match status with
        | .Err e => ok (.Err (.LaneTransition e))
        | .Ok _ => ok (.Ok ())
      (r,[.lane d,.late arg out])

def bindings (pay : Statement → Result (core.result.Result (Array U8 216#usize) PaymentError))
    (lane : Array U32 8#usize → Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1))
    (late : NFY_NBN_LateSummary.Statement → Slice U8 → Result (core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 × Slice U8)) (s : Statement) : R × List Call :=
  if (parts s).1 ≠ (common s).master_account then (ok (.Err .MasterBindingMismatch),[])
  else if (parts s).2.1 ≠ (common s).lane_transition.live_snapshot.deployment_domain then (ok (.Err .DeploymentBindingMismatch),[])
  else if (common s).lane_transition.live_snapshot.pool ≠ (common s).master_account then (ok (.Err .MasterBindingMismatch),[])
  else if (parts s).2.2.1 ≠ (common s).checkpoint_sequence then (ok (.Err .CheckpointBindingMismatch),[])
  else if (parts s).2.2.2.1 ≠ (common s).historical_global_anchor then (ok (.Err .HistoricalAnchorMismatch),[])
  else tail pay lane late s

def run (pay : Statement → Result (core.result.Result (Array U8 216#usize) PaymentError))
    (lane : Array U32 8#usize → Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1))
    (late : NFY_NBN_LateSummary.Statement → Slice U8 → Result (core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 × Slice U8)) (s : Statement) : R × List Call :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then (ok (.Err .NonZeroBinding),[])
  else if 8 ≤ (common s).output_lane.val then (ok (.Err .InvalidOutputLane),[])
  else match pay s with
    | .fail e => (.fail e,[.payment s])
    | .div => (.div,[.payment s])
    | .ok (.Err e) => (ok (.Err (.Payment e)),[.payment s])
    | .ok (.Ok _) => ((bindings pay lane late s).1,.payment s :: (bindings pay lane late s).2)


/-- Full oracle substitution, retaining all failed/diverging child prefixes. -/
theorem substitution (s : Statement) :
    run NFY_NED_ValidatorTrace.payment (NFY_NBN_FirstByteDependency.lane enc) (NFY_NBN_LateSummary.run enc) s =
    NFY_NED_ValidatorTrace.run s := by rfl

/-- Result projection of the same oracle execution. -/
theorem result (s : Statement) :
    (run NFY_NED_ValidatorTrace.payment (NFY_NBN_FirstByteDependency.lane enc) (NFY_NBN_LateSummary.run enc) s).1 =
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [substitution,NFY_NED_ValidatorTrace.erases]

/-- Exact ordered argument-bearing call log, not only an acceptance decision. -/
theorem effects (s : Statement) :
    (run NFY_NED_ValidatorTrace.payment (NFY_NBN_FirstByteDependency.lane enc) (NFY_NBN_LateSummary.run enc) s).2 =
    (NFY_NED_ValidatorTrace.run s).2 := by rw [substitution]

#print axioms substitution
#print axioms result
#print axioms effects
end NFY_NEE_ValidatorOracle
-- END copied NEE_ValidatorOracle
-- BEGIN copied NEE_ValidatorMutation: evidence/slice-s-compose2-20261029/NEE_ValidatorMutation.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ValidatorMutation
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
abbrev LateError := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
abbrev LateReply := Result (core.result.Result Unit LateError × Slice U8)

def mutate (f : Slice U8 → Slice U8) : LateReply → LateReply
  | .fail e => .fail e
  | .div => .div
  | .ok (status,out) => .ok (status,f out)

def ignore (r : LateReply) : NFY_NED_ValidatorTrace.R := do
  let (status,_) ← r
  match status with
  | .Err e => ok (.Err (.LaneTransition e))
  | .Ok _ => ok (.Ok ())

/-- The local buffer never escapes the validator, even on a child error. -/
theorem discard (r : LateReply) (f : Slice U8 → Slice U8) :
    ignore (mutate f r) = ignore r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok p => rcases p with ⟨status,out⟩; cases status <;> rfl

abbrev Pay := Statement → Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Lane := Array U32 8#usize → Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
abbrev Late := NFY_NBN_LateSummary.Statement → Slice U8 → LateReply

theorem tail (pay : Pay) (lane : Lane) (late : Late) (f : Slice U8 → Slice U8)
    (s : Statement) :
    NFY_NEE_ValidatorOracle.tail pay lane (fun a b => mutate f (late a b)) s =
    NFY_NEE_ValidatorOracle.tail pay lane late s := by
  unfold NFY_NEE_ValidatorOracle.tail
  dsimp only
  cases h : lane (parts s).2.2.2.2.1 with
  | fail e => simp only [h]
  | div => simp only [h]
  | ok p => cases p with
    | Err e => simp only [h]
    | Ok l =>
      simp only [h]
      split
      · rfl
      · change (ignore (mutate f (late _ _)),_) = (ignore (late _ _),_)
        rw [discard]

theorem bindings (pay : Pay) (lane : Lane) (late : Late) (f : Slice U8 → Slice U8)
    (s : Statement) :
    NFY_NEE_ValidatorOracle.bindings pay lane (fun a b => mutate f (late a b)) s =
    NFY_NEE_ValidatorOracle.bindings pay lane late s := by
  unfold NFY_NEE_ValidatorOracle.bindings
  repeat' first | split | rfl | exact tail pay lane late f s

/-- Arbitrary whole-buffer reply mutations preserve Result AND ordered calls. -/
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late)
    (f : Slice U8 → Slice U8) (s : Statement) :
    NFY_NEE_ValidatorOracle.run pay lane (fun a b => mutate f (late a b)) s =
    NFY_NEE_ValidatorOracle.run pay lane late s := by
  unfold NFY_NEE_ValidatorOracle.run
  split
  · rfl
  · split
    · rfl
    · cases pay s with
      | fail e => rfl
      | div => rfl
      | ok p => cases p with
        | Err e => rfl
        | Ok bytes => rw [bindings]

#print axioms discard
#print axioms tail
#print axioms bindings
#print axioms result_and_effects
end NFY_NEE_ValidatorMutation
-- END copied NEE_ValidatorMutation
-- BEGIN copied NEE_OracleCallDomains: evidence/slice-s-compose2-20261029/NEE_OracleCallDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_OracleCallDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_ValidatorTrace NFY_NEE_ValidatorMutation
open NFY_NEE_ValidatorOracle

def TailShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.lane (parts s).2.2.2.2.1] ∨
  xs = [.lane (parts s).2.2.2.2.1,.late (common s).lane_transition NFY_NBN_LateResult.zero]

def Shape (s : Statement) (xs : List Call) : Prop :=
  xs = [] ∨ xs = [.payment s] ∨
  xs = [.payment s,.lane (parts s).2.2.2.2.1] ∨
  xs = [.payment s,.lane (parts s).2.2.2.2.1,.late (common s).lane_transition NFY_NBN_LateResult.zero]

theorem tail_shape (pay : Pay) (lane : Lane) (late : Late) (s : Statement) : TailShape s (NFY_NEE_ValidatorOracle.tail pay lane late s).2 := by
  unfold NFY_NEE_ValidatorOracle.tail
  dsimp only
  cases h : lane (parts s).2.2.2.2.1 with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok r => cases r with
    | Err e => simp only [h]; exact Or.inl rfl
    | Ok l =>
      simp only [h]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem bindings_shape (pay : Pay) (lane : Lane) (late : Late) (s : Statement) :
    (NFY_NEE_ValidatorOracle.bindings pay lane late s).2 = [] ∨ TailShape s (NFY_NEE_ValidatorOracle.bindings pay lane late s).2 := by
  unfold NFY_NEE_ValidatorOracle.bindings
  repeat' first | split | exact Or.inl rfl | exact Or.inr (tail_shape pay lane late s)

theorem shape (pay : Pay) (lane : Lane) (late : Late) (s : Statement) : Shape s (NFY_NEE_ValidatorOracle.run pay lane late s).2 := by
  unfold NFY_NEE_ValidatorOracle.run
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · cases h : pay s with
      | fail e => simp only [h]; exact Or.inr (Or.inl rfl)
      | div => simp only [h]; exact Or.inr (Or.inl rfl)
      | ok r => cases r with
        | Err e => simp only [h]; exact Or.inr (Or.inl rfl)
        | Ok bytes =>
          simp only [h]
          rcases bindings_shape pay lane late s with none | one | two
          · rw [none]; exact Or.inr (Or.inl rfl)
          · rw [one]; exact Or.inr (Or.inr (Or.inl rfl))
          · rw [two]; exact Or.inr (Or.inr (Or.inr rfl))

/-- A logged late call has the SAME full record and fixed local output width.
The whole root need not accept: an error returned by that call is retained. -/
theorem late_domain (pay : Pay) (lane : Lane) (late : Late) (s : Statement) (arg : NFY_NBN_LateSummary.Statement) (out : Slice U8)
    (reached : Call.late arg out ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2) :
    arg = (common s).lane_transition ∧ out = NFY_NBN_LateResult.zero ∧ out.length = 1520 := by
  rcases shape pay lane late s with none | one | two | three
  · simp only [none,List.not_mem_nil] at reached
  · simp only [one,List.mem_singleton,reduceCtorEq] at reached
  · simp only [two,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at reached
  · simp only [three,List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.late.injEq] at reached
    obtain ⟨rfl,rfl⟩ := reached
    refine ⟨rfl,rfl,?_⟩
    simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
    rfl

theorem payment_same (pay : Pay) (lane : Lane) (late : Late) (s : Statement) (arg : Statement)
    (reached : Call.payment arg ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2) : arg = s := by
  rcases shape pay lane late s with none | one | two | three <;>
    simp_all only [List.mem_cons,List.not_mem_nil,
      reduceCtorEq,false_or,or_false,Call.payment.injEq]

/-- Every lane call uses the same nullifier, even for arbitrary failing
child replies. This is a caller-domain fact, not a child success premise. -/
theorem lane_same (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (arg : Array U32 8#usize)
    (reached : Call.lane arg ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2) :
    arg = (parts s).2.2.2.2.1 := by
  rcases shape pay lane late s with none | one | two | three <;>
    simp_all only [List.mem_cons,List.not_mem_nil,
      reduceCtorEq,false_or,or_false,Call.lane.injEq]

#print axioms lane_same
#print axioms tail_shape
#print axioms bindings_shape
#print axioms shape
#print axioms late_domain
#print axioms payment_same
end NFY_NEE_OracleCallDomains
-- END copied NEE_OracleCallDomains
-- BEGIN copied NEE_ReachedSubstitution: evidence/slice-s-compose2-20261029/NEE_ReachedSubstitution.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ReachedSubstitution
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_ValidatorTrace NFY_NEE_ValidatorMutation
attribute [local instance] Classical.propDecidable

/-- Full child equality is required only where the native caller reaches
that exact argument. The temporary late output is discarded by the caller. -/
def ReplyLaw (pay : Pay) (lane : Lane) (late : Late) : Call → Prop
  | .payment a => pay a = NFY_NED_ValidatorTrace.payment a
  | .lane d => lane d = NFY_NBN_FirstByteDependency.lane enc d
  | .late a out => ignore (late a out) = ignore (NFY_NBN_LateSummary.run enc a out)

def Children (pay : Pay) (lane : Lane) (late : Late) (s : Statement) : Prop :=
  ∀ c, c ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2 → ReplyLaw pay lane late c

theorem tail (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (lane_bridge : lane (parts s).2.2.2.2.1 =
      NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1)
    (late_bridge : ∀ a out, Call.late a out ∈ (NFY_NEE_ValidatorOracle.tail pay lane late s).2 →
      ignore (late a out) = ignore (NFY_NBN_LateSummary.run enc a out)) :
    NFY_NEE_ValidatorOracle.tail pay lane late s = NFY_NED_ValidatorTrace.tail s := by
  unfold NFY_NEE_ValidatorOracle.tail NFY_NED_ValidatorTrace.tail
  dsimp only
  rw [lane_bridge]
  cases h : NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1 with
  | fail e => simp only [h]
  | div => simp only [h]
  | ok r => cases r with
    | Err e => simp only [h]
    | Ok l =>
      simp only [h]
      split
      · rfl
      · rename_i same
        have reached : Call.late (common s).lane_transition NFY_NBN_LateResult.zero ∈
            (NFY_NEE_ValidatorOracle.tail pay lane late s).2 := by
          simp only [NFY_NEE_ValidatorOracle.tail,lane_bridge,h,bind_tc_ok,same,if_false]
          simp
        change (ignore (late _ _),_) = (ignore (NFY_NBN_LateSummary.run enc _ _),_)
        rw [late_bridge _ _ reached]

theorem bindings (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (children : ∀ c, c ∈ (NFY_NEE_ValidatorOracle.bindings pay lane late s).2 →
      ReplyLaw pay lane late c) :
    NFY_NEE_ValidatorOracle.bindings pay lane late s = NFY_NED_ValidatorTrace.bindings s := by
  unfold NFY_NEE_ValidatorOracle.bindings at children ⊢
  unfold NFY_NED_ValidatorTrace.bindings
  repeat' first | rfl | split
  have child_tail : ∀ c, c ∈ (NFY_NEE_ValidatorOracle.tail pay lane late s).2 →
      ReplyLaw pay lane late c := by
    simpa [*] using children
  have reached : Call.lane (parts s).2.2.2.2.1 ∈ (NFY_NEE_ValidatorOracle.tail pay lane late s).2 := by
    rcases NFY_NEE_OracleCallDomains.tail_shape pay lane late s with one | two <;>
      simp only [*,List.mem_cons,List.mem_singleton,true_or]
  exact tail pay lane late s (child_tail _ reached) (fun a out h => child_tail _ h)

/-- Exact caller Result and ordered arguments after substituting ONLY reached
child bridges. These are explicit inner hypotheses, not PhysicalInterpretation.
Native association and child framed contracts are separate evidence gates. -/
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (children : Children pay lane late s) :
    NFY_NEE_ValidatorOracle.run pay lane late s = NFY_NED_ValidatorTrace.run s := by
  by_cases h0 : (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero
  · simp only [NFY_NEE_ValidatorOracle.run,NFY_NED_ValidatorTrace.run,h0,if_true]
  by_cases h1 : 8 ≤ (common s).output_lane.val
  · simp only [NFY_NEE_ValidatorOracle.run,NFY_NED_ValidatorTrace.run,h0,h1,if_false,if_true]
  have reached : Call.payment s ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2 := by
    simp only [NFY_NEE_ValidatorOracle.run,h0,h1,if_false]
    cases pay s with
    | fail e => simp
    | div => simp
    | ok r => cases r <;> simp
  have hp : pay s = NFY_NED_ValidatorTrace.payment s := children _ reached
  cases hpay : NFY_NED_ValidatorTrace.payment s with
  | fail e => simp only [NFY_NEE_ValidatorOracle.run,NFY_NED_ValidatorTrace.run,h0,h1,if_false,hp,hpay]
  | div => simp only [NFY_NEE_ValidatorOracle.run,NFY_NED_ValidatorTrace.run,h0,h1,if_false,hp,hpay]
  | ok r => cases r with
    | Err e => simp only [NFY_NEE_ValidatorOracle.run,NFY_NED_ValidatorTrace.run,h0,h1,if_false,hp,hpay]
    | Ok bytes =>
      have hb : ∀ c, c ∈ (NFY_NEE_ValidatorOracle.bindings pay lane late s).2 → ReplyLaw pay lane late c := by
        intro c hc
        apply children c
        simp only [NFY_NEE_ValidatorOracle.run,h0,h1,if_false,hp,hpay]
        exact List.mem_cons_of_mem _ hc
      simp only [NFY_NEE_ValidatorOracle.run,NFY_NED_ValidatorTrace.run,h0,h1,if_false,hp,hpay,
        bindings pay lane late s hb]

#print axioms bindings
#print axioms result_and_effects
#print axioms tail
end NFY_NEE_ReachedSubstitution
-- END copied NEE_ReachedSubstitution
-- BEGIN copied NEE_ReachedRootModel: evidence/slice-s-compose2-20261029/NEE_ReachedRootModel.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ReachedRootModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_ValidatorTrace NFY_NEE_ValidatorMutation

/-- Ruling-(y) MODEL substitution with every open child law exposed by name.
This theorem does not claim that a Rust child, frame or physical instance has
been proved. The three laws must come from independently accepted bridges. -/
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (payment_bridge : ∀ a, Call.payment a ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2 →
      pay a = NFY_NED_ValidatorTrace.payment a)
    (output_lane_bridge : ∀ d, Call.lane d ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2 →
      lane d = NFY_NBN_FirstByteDependency.lane enc d)
    (late_bridge : ∀ a out, Call.late a out ∈ (NFY_NEE_ValidatorOracle.run pay lane late s).2 →
      ignore (late a out) = ignore (NFY_NBN_LateSummary.run enc a out)) :
    NFY_NEE_ValidatorOracle.run pay lane late s =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       (NFY_NED_ValidatorTrace.run s).2) := by
  have joined := NFY_NEE_ReachedSubstitution.result_and_effects pay lane late s
    (by
      intro c reached
      cases c with
      | payment a => exact payment_bridge a reached
      | lane d => exact output_lane_bridge d reached
      | late a out => exact late_bridge a out reached)
  rw [joined]
  exact Prod.ext (NFY_NED_ValidatorTrace.erases s) rfl

#print axioms result_and_effects
end NFY_NEE_ReachedRootModel
-- END copied NEE_ReachedRootModel
-- BEGIN copied NEM_PaymentReached: evidence/slice-s-compose5-20261102/NEM_PaymentReached.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEM_PaymentReached
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult

def pay (s : Statement) :=
  NFY_NBN_ValidatorSummary.paymentWith
    pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
    pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 s

/-- Exact emitted payment child selected by this statement, including every
rejection and all returned bytes. Native certificates remain separate. -/
theorem payment_instance (s : Statement) : pay s = NFY_NED_ValidatorTrace.payment s := by
  cases s with
  | PrivateTransfer c p =>
    exact (NFY_NED_CodecComposition.transfer_law p).symm
  | Withdrawal c p =>
    exact (NFY_NED_CodecComposition.withdrawal_law p).symm

/-- The first reached-child law is supplied on the SAME argument; no payment
PacketDomain, accepted-result, or independent execution premise remains. -/
theorem payment_reached (lane : NFY_NEE_ValidatorMutation.Lane)
    (late : NFY_NEE_ValidatorMutation.Late) (s a : Statement)
    (_reached : NFY_NED_ValidatorTrace.Call.payment a ∈
      (NFY_NEE_ValidatorOracle.run pay lane late s).2) :
    pay a = NFY_NED_ValidatorTrace.payment a := payment_instance a

#print axioms payment_instance
#print axioms payment_reached
end NFY_NEM_PaymentReached
-- END copied NEM_PaymentReached
-- BEGIN copied NEM_LaneReached: evidence/slice-s-compose5-20261102/NEM_LaneReached.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEM_LaneReached
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult

def lane (d : Array U32 8#usize) :=
  pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d

theorem lane_instance (d : Array U32 8#usize) :
    lane d = NFY_NBN_FirstByteDependency.lane NFY_NED_ValidatorTrace.enc d :=
  (NFY_NED_SubtreeComposition.output_lane d).symm

theorem lane_reached (late : NFY_NEE_ValidatorMutation.Late) (s : Statement)
    (d : Array U32 8#usize)
    (_reached : NFY_NED_ValidatorTrace.Call.lane d ∈
      (NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay lane late s).2) :
    lane d = NFY_NBN_FirstByteDependency.lane NFY_NED_ValidatorTrace.enc d := lane_instance d

#print axioms lane_instance
#print axioms lane_reached
end NFY_NEM_LaneReached
-- END copied NEM_LaneReached
-- BEGIN copied NEJ_CommonFrame: evidence/slice-s-compose3-20261101/NEJ_CommonFrame.lean
set_option autoImplicit false
namespace NFY_NEJ_CommonFrame
open KMX_CopyMeaning

/-- Source-order write windows of frozen payment_relation::encode_common.
Digest computations precede their respective copy windows and are separate
child obligations. This describes byte writes only. -/
def windows : List (Nat × Nat) :=
  [(0,4),(4,1),(5,1),(6,1),(8,32),(40,32),(72,8),(80,32),(112,32),(144,4)]

def touched (ws : List (Nat × Nat)) (k : Nat) : Prop :=
  ∃ w ∈ ws, w.1 ≤ k ∧ k < w.1 + w.2

instance (ws : List (Nat × Nat)) (k : Nat) : Decidable (touched ws k) :=
  inferInstanceAs (Decidable (∃ w ∈ ws, w.1 ≤ k ∧ k < w.1 + w.2))

def run {α : Type} (src dst : Nat → α) : List (Nat × Nat) → Nat → α
  | [] => dst
  | w :: ws => run src (loop src dst w.1 w.2) ws

/-- Arbitrary indexed prestate; no whole-buffer reduction or native unwinding. -/
theorem run_spec {α : Type} (src dst : Nat → α) (ws : List (Nat × Nat)) (k : Nat) :
    run src dst ws k = if touched ws k then src k else dst k := by
  induction ws generalizing dst with
  | nil => simp [run, touched]
  | cons w ws ih =>
    rw [run, ih, loop_spec]
    by_cases ht : touched ws k
    · have h : touched (w :: ws) k := by
        obtain ⟨v,hv,h⟩ := ht
        exact ⟨v,List.mem_cons_of_mem w hv,h⟩
      simp [ht,h]
    · by_cases hw : w.1 ≤ k ∧ k < w.1 + w.2
      · have h : touched (w :: ws) k := ⟨w,List.mem_cons_self,hw⟩
        simp [ht,hw,h]
      · have h : ¬ touched (w :: ws) k := by
          rintro ⟨v,hv,hv'⟩
          rcases List.mem_cons.mp hv with heq | hm
          · subst v; exact hw hv'
          · exact ht ⟨v,hm,hv'⟩
        simp [ht,hw,h]

/-- Exact union of the ten frozen write ranges, including reserved-byte gaps. -/
theorem touched_windows (k : Nat) :
    touched windows k ↔ k < 7 ∨ (8 ≤ k ∧ k < 148) := by
  simp only [touched, windows, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨w,hw,hr⟩
    rcases hw with h | h | h | h | h | h | h | h | h | h
    all_goals subst w; dsimp at hr; omega
  · intro h
    rcases h with h | h
    · by_cases h0 : k < 4
      · exact ⟨(0,4),by simp,by dsimp; omega⟩
      · by_cases h4 : k = 4
        · exact ⟨(4,1),by simp,by dsimp; omega⟩
        · by_cases h5 : k = 5
          · exact ⟨(5,1),by simp,by dsimp; omega⟩
          · exact ⟨(6,1),by simp,by dsimp; omega⟩
    · by_cases h40 : k < 40
      · exact ⟨(8,32),by simp,by dsimp; omega⟩
      · by_cases h72 : k < 72
        · exact ⟨(40,32),by simp,by dsimp; omega⟩
        · by_cases h80 : k < 80
          · exact ⟨(72,8),by simp,by dsimp; omega⟩
          · by_cases h112 : k < 112
            · exact ⟨(80,32),by simp,by dsimp; omega⟩
            · by_cases h144 : k < 144
              · exact ⟨(112,32),by simp,by dsimp; omega⟩
              · exact ⟨(144,4),by simp,by dsimp; omega⟩

theorem common_bytes {α : Type} (src dst : Nat → α) (k : Nat) :
    run src dst windows k =
      if k < 7 ∨ (8 ≤ k ∧ k < 148) then src k else dst k := by
  simp only [run_spec, touched_windows]

/-- Byte 7 and the entire suffix from 148 survive arbitrary child reply bytes. -/
theorem reserved_frame {α : Type} (src dst : Nat → α) (k : Nat)
    (outside : k = 7 ∨ 148 ≤ k) : run src dst windows k = dst k := by
  rw [common_bytes, if_neg]
  omega

/-- Distinct windows can be joined without assuming their initial bytes zero. -/
theorem window_disjoint {α : Type} (src dst : Nat → α) (a n b m k : Nat)
    (inside : b ≤ k ∧ k < b + m) (disjoint : a+n ≤ b ∨ b+m ≤ a) :
    loop src dst a n k = dst k := by
  apply copy_frame
  omega

#print axioms run_spec
#print axioms touched_windows
#print axioms common_bytes
#print axioms reserved_frame
#print axioms window_disjoint
end NFY_NEJ_CommonFrame
-- END copied NEJ_CommonFrame
-- BEGIN copied NEJ_ArrayFrame: evidence/slice-s-compose3-20261101/NEJ_ArrayFrame.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEJ_ArrayFrame
open Aeneas Aeneas.Std Result

theorem list_frame {α : Type} (dst src : List α) (start k : Nat)
    (fits : start + src.length ≤ dst.length)
    (outside : k < start ∨ start + src.length ≤ k) :
    (dst.setSlice! start src)[k]? = dst[k]? := by
  have hs : start ≤ dst.length := by omega
  have hroom : min src.length (dst.length-start) = src.length := Nat.min_eq_left (by omega)
  simp only [List.setSlice!, hroom, List.take_length]
  rw [List.append_assoc]
  have hlen : (dst.take start).length = start := by
    exact (List.length_take).trans (Nat.min_eq_left hs)
  rcases outside with before | after
  · rw [List.getElem?_append_left (by rw [hlen]; exact before)]
    exact List.getElem?_take_of_lt before
  · rw [List.getElem?_append_right (by rw [hlen]; omega)]
    rw [List.getElem?_append_right (by rw [hlen]; omega)]
    rw [List.getElem?_drop, hlen]
    congr 1
    omega

/-- Concrete emitted back-write frame, independent of the allocation's values. -/
theorem array_frame {N : Usize} (dst : Array U8 N) (src : List U8) (start k : Nat)
    (fits : start + src.length ≤ N.val)
    (outside : k < start ∨ start + src.length ≤ k) :
    (dst.setSlice! start src).val[k]? = dst.val[k]? := by
  change (dst.val.setSlice! start src)[k]? = dst.val[k]?
  exact list_frame dst.val src start k (by simpa only [dst.property] using fits) outside

#print axioms list_frame
#print axioms array_frame
end NFY_NEJ_ArrayFrame
-- END copied NEJ_ArrayFrame
-- BEGIN copied NED_ExecutionComposition: evidence/slice-s-compose-20261029/NED_ExecutionComposition.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_ExecutionComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- The state and ordered effects are explicit. This is a transport carrier,
not a claim that Rust execution has been instantiated on this carrier. -/
structure Observation (R State Effect : Type) where
  result : R
  state : State
  effects : List Effect
  deriving DecidableEq

def validatorReference (s : NFY_NBN_StatementResult.Statement) :=
  NFY_NBN_ValidatorSummary.run atomic_statement.encode_digest_canonical
    (fun p => ok (NFY_NBP_PaymentModel.transfer_encoded p))
    (fun p => ok (NFY_NBP_PaymentModel.withdrawal_encoded p)) s

def encoderReference (s : NFY_NBN_StatementResult.Statement) :=
  NFY_NBN_StatementEncoderSummary.run atomic_statement.encode_digest_canonical
    (fun p => ok (NFY_NBP_PaymentModel.transfer_encoded p))
    (fun p => ok (NFY_NBP_PaymentModel.withdrawal_encoded p)) s

/-- Conditional transport of an already established SAME reference execution.
The physical equality is explicit; absent its concrete native certificate this
is not a CLOSED native root and must not be booked as one. -/
theorem validator_observation {State Effect : Type}
    (s : NFY_NBN_StatementResult.Statement) (st : State) (events : List Effect)
    (native : Observation (Result (core.result.Result Unit NFY_NBN_StatementResult.Error)) State Effect)
    (sameReferenceObservation : native = ⟨validatorReference s,st,events⟩) :
    native = ⟨pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,st,events⟩ := by
  rw [sameReferenceObservation]
  exact congrArg (fun r => Observation.mk r st events) (NFY_NED_CodecComposition.validator s)

theorem encoder_observation {State Effect : Type}
    (s : NFY_NBN_StatementResult.Statement) (st : State) (events : List Effect)
    (native : Observation NFY_NBN_StatementEncoderSummary.BytesResult State Effect)
    (sameReferenceObservation : native = ⟨encoderReference s,st,events⟩) :
    native = ⟨NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),st,events⟩ := by
  rw [sameReferenceObservation]
  exact congrArg (fun r => Observation.mk r st events) (NFY_NED_CodecComposition.encoder s)

#print axioms validator_observation
#print axioms encoder_observation
end NFY_NED_ExecutionComposition
-- END copied NED_ExecutionComposition
-- BEGIN copied NED_EncoderTrace: evidence/slice-s-compose-20261029/NED_EncoderTrace.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_EncoderTrace
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
abbrev R := NFY_NBN_StatementEncoderSummary.BytesResult
inductive Call where
  | validate (s : Statement)
  | digest (d : Array U32 8#usize)
  | late (s : NFY_NBN_LateSummary.Statement) (out : Slice U8)
  | payment (s : Statement)
def enc := atomic_statement.encode_digest_canonical
def transfer (p : NFY_NBN_ValidatorSummary.Transfer) := ok (NFY_NBP_PaymentModel.transfer_encoded p)
def withdrawal (p : NFY_NBN_ValidatorSummary.Withdrawal) := ok (NFY_NBP_PaymentModel.withdrawal_encoded p)
def payment (s : Statement) := NFY_NBN_ValidatorSummary.paymentWith transfer withdrawal s

def payStep (s : Statement) (anchor : Array U8 32#usize) (late : Slice U8) : R × List Call :=
  let r : R := do
    let pay ← payment s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok a => ok (.Ok ((NFY_NBN_StatementEncoderSummary.prefixBytes s anchor ++ late.val) ++ a.val))
  (r,[.payment s])

def lateStep (s : Statement) (anchor : Array U8 32#usize) : R × List Call :=
  let arg := (common s).lane_transition
  let out := NFY_NBN_LateResult.zero
  match NFY_NBN_LateSummary.run enc arg out with
  | .fail e => (.fail e,[.late arg out])
  | .div => (.div,[.late arg out])
  | .ok (.Err e,_) => (ok (.Err (.LaneTransition e)),[.late arg out])
  | .ok (.Ok _,late) => ((payStep s anchor late).1,.late arg out :: (payStep s anchor late).2)

def anchorStep (s : Statement) : R × List Call :=
  let d := (common s).historical_global_anchor
  match enc d with
  | .fail e => (.fail e,[.digest d])
  | .div => (.div,[.digest d])
  | .ok anchor => ((lateStep s anchor).1,.digest d :: (lateStep s anchor).2)

def run (s : Statement) : R × List Call :=
  let validation := NFY_NED_ExecutionComposition.validatorReference s
  match validation with
  | .fail e => (.fail e,[.validate s])
  | .div => (.div,[.validate s])
  | .ok (.Err e) => (ok (.Err e),[.validate s])
  | .ok (.Ok _) => ((anchorStep s).1,.validate s :: (anchorStep s).2)

def lateRef (s : Statement) (anchor : Array U8 32#usize) : R := do
  let (status,late) ← NFY_NBN_LateSummary.run enc (common s).lane_transition NFY_NBN_LateResult.zero
  match status with
  | .Err e => ok (.Err (.LaneTransition e))
  | .Ok _ => (payStep s anchor late).1

theorem late_erases (s : Statement) (anchor : Array U8 32#usize) :
    (lateStep s anchor).1 = lateRef s anchor := by
  unfold lateStep lateRef
  dsimp only
  cases h : NFY_NBN_LateSummary.run enc (common s).lane_transition NFY_NBN_LateResult.zero with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok pair => cases pair with
    | mk status late => cases status <;> simp only [h,bind_tc_ok,Aeneas.Std.uncurry]

theorem anchor_erases (s : Statement) :
    (anchorStep s).1 = (do let anchor ← enc (common s).historical_global_anchor; lateRef s anchor) := by
  unfold anchorStep
  dsimp only
  cases h : enc (common s).historical_global_anchor with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok anchor => simp only [h,bind_tc_ok]; exact late_erases s anchor

theorem erases (s : Statement) : (run s).1 =
    NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s) := by
  rw [← NFY_NED_CodecComposition.encoder s]
  change (run s).1 = NFY_NBN_StatementEncoderSummary.run enc transfer withdrawal s
  unfold run NFY_NBN_StatementEncoderSummary.run
  dsimp only
  cases h : NFY_NED_ExecutionComposition.validatorReference s with
  | fail e => change NFY_NBN_ValidatorSummary.run enc transfer withdrawal s = _ at h; simp only [h,bind_tc_fail]
  | div => change NFY_NBN_ValidatorSummary.run enc transfer withdrawal s = _ at h; simp only [h,bind_tc_div]
  | ok r => cases r with
    | Err e => change NFY_NBN_ValidatorSummary.run enc transfer withdrawal s = _ at h; simp only [h,bind_tc_ok]
    | Ok u =>
      change NFY_NBN_ValidatorSummary.run enc transfer withdrawal s = _ at h
      simp only [h,bind_tc_ok]
      rw [anchor_erases]
      rfl

#print axioms late_erases
#print axioms anchor_erases
#print axioms erases
end NFY_NED_EncoderTrace
-- END copied NED_EncoderTrace

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
