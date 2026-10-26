import R1Z.PV_RunJoin_CallerWorld
import R1Z.PV_RunJoin_FiniteGraph
import R1Z.PV_RunJoin_Coupling
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompletedWorld
open Aeneas Aeneas.Std Result
open ProverRwRngCaller
open R1Z.ProverRwRngCallerControl R1Z.ProverRwRngCallerReplay
variable [NativeTypes] [ErasureFns]

/-- Initialization from completion coins, including native statuses and partial
writes. Association with the native conditional law is a separate obligation;
arbitrary statuses are never declared uniformly sampled OS outcomes. -/
structure Data (Coins N L B : Type) where
  replies : Coins → Fin 128 → (Array U8 64#usize × core.result.Result Unit getrandom.error.Error)
  policy : Coins → N
  ledger : Coins → L
  body : Coins → B

def provider {Coins N L B : Type} (d : Data Coins N L B) (r : Coins) : Tape :=
  ⟨⟨List.ofFn (d.replies r),by simp only [List.length_ofFn]; scalar_tac⟩,0#usize⟩

def initialState {Coins N L B : Type} (d : Data Coins N L B) (r : Coins) : Tape × N × L × B :=
  (provider d r,d.policy r,d.ledger r,d.body r)

/-- The graph retains its explicit provider/zero cursor/policy/ledger/body
state and its latent completion coordinate. It needs no finite-state or
uniform-law assumption on the whole filesystem. -/
abbrev World {Coins N L B : Type} (d : Data Coins N L B) :=
  PV_RunJoin_FiniteGraph.World (initialState d)

def create {Coins N L B : Type} (d : Data Coins N L B) (r : Coins) : World d :=
  PV_RunJoin_FiniteGraph.create (initialState d) r

def coordinates {Coins N L B : Type} (d : Data Coins N L B) : World d ≃ Coins :=
  PV_RunJoin_FiniteGraph.coordinates (initialState d)

def execute {Coins N L B : Type} {d : Data Coins N L B}
    (policy : Policy N) (body : Body B L) (w : World d) : Result (Output N L B) :=
  prove_masked_retrying_with policy body true w.state.1 w.state.2.1 w.state.2.2.1 w.state.2.2.2

theorem initial_capacity {Coins N L B : Type} {d : Data Coins N L B} (w : World d) :
    w.state.1.used.val = 0 ∧ w.state.1.replies.val.length = 128 := by
  rw [w.state_eq]
  exact ⟨rfl,by simp only [initialState,provider,List.length_ofFn]⟩

theorem execution_replay {Coins N L B : Type} {d : Data Coins N L B}
    (policy : Policy N) (body : Body B L) (w : World d) (out : Output N L B)
    (run : execute policy body w = .ok out) :
    ∃ states, Replay policy body (w.state.1,w.state.2.1,w.state.2.2.1,w.state.2.2.2,0#usize) states out ∧
      callbacks states ≤ 8 := cap8 policy body _ _ _ _ out run

#print axioms provider
#print axioms create
#print axioms coordinates
#print axioms initial_capacity
#print axioms execution_replay
end R1Z.PV_RunJoin_CompletedWorld
