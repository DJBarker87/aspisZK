import R1Z.ProverCommitPublication33
/-! Ordered native leaf salt consumption and writes. Every coin result and
updated coin state is retained. The coin function is shared, not assumed
uniform or identified with a native source merely by this theorem. -/
set_option autoImplicit false
namespace R1Z.ProverCommitLeaves43
open ProverCommitTrustedStd24
variable {Key Bytes Salt Coins State Thread Slot Output : Type}
variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

abbrev PairState (State Coins : Type) := State × State × Coins

def pairStep (map : MapAPI Key (Bytes × Salt) State cmp)
    (coin : Coins → Salt × Coins) (state : PairState State Coins)
    (entry : Key × (Bytes × Bytes)) : PairState State Coins :=
  let (salt1,s1) := coin state.2.2
  let (salt2,s2) := coin s1
  ((map.insert state.1 entry.1 (entry.2.1,salt1)).1,
    (map.insert state.2.1 entry.1 (entry.2.2,salt2)).1,s2)

def foldedStep (map : MapAPI Key (Bytes × Salt) State cmp)
    (coin : Coins → Salt × Coins) (state : State × Coins)
    (entry : Key × Bytes) : State × Coins :=
  let (salt,after) := coin state.2
  ((map.insert state.1 entry.1 (entry.2,salt)).1,after)

def decodePair (map : MapAPI Key (Bytes × Salt) State cmp)
    (state : PairState State Coins) := (map.decode state.1,map.decode state.2.1,state.2.2)

def decodeFolded (map : MapAPI Key (Bytes × Salt) State cmp)
    (state : State × Coins) := (map.decode state.1,state.2)

/-- A general finite caller composition, with its one-step law explicit.
The concrete laws below discharge this premise using only TrustedStd. -/
theorem fold_decode {A S T : Type} (decode : S → T) (step : S → A → S)
    (model : T → A → T) (law : ∀ s a, decode (step s a) = model (decode s) a)
    (xs : List A) (state : S) :
    decode (xs.foldl step state) = xs.foldl model (decode state) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,law]

variable [DecidableEq Thread]
variable (map : MapAPI Key (Bytes × Salt) State cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (trusted : TrustedStd map tls thread schedule)
include trusted

theorem pair_step (coin : Coins → Salt × Coins) (state : PairState State Coins)
    (entry : Key × (Bytes × Bytes)) :
    decodePair map (pairStep map coin state entry) =
      pairStep modelMap coin (decodePair map state) entry := by
  simp only [decodePair,pairStep,trusted.btree_insert_state,modelMap,
    ProverCommitTreeOps23.treeInsert]

theorem folded_step (coin : Coins → Salt × Coins) (state : State × Coins)
    (entry : Key × Bytes) :
    decodeFolded map (foldedStep map coin state entry) =
      foldedStep modelMap coin (decodeFolded map state) entry := by
  simp only [decodeFolded,foldedStep,trusted.btree_insert_state,modelMap,
    ProverCommitTreeOps23.treeInsert]

theorem pair_loop (coin : Coins → Salt × Coins) (state : PairState State Coins)
    (entries : List (Key × (Bytes × Bytes))) :
    decodePair map (entries.foldl (pairStep map coin) state) =
      entries.foldl (pairStep modelMap coin) (decodePair map state) :=
  fold_decode (decodePair map) (pairStep map coin) (pairStep modelMap coin)
    (pair_step map tls thread schedule trusted coin) entries state

theorem folded_loop (coin : Coins → Salt × Coins) (state : State × Coins)
    (entries : List (Key × Bytes)) :
    decodeFolded map (entries.foldl (foldedStep map coin) state) =
      entries.foldl (foldedStep modelMap coin) (decodeFolded map state) :=
  fold_decode (decodeFolded map) (foldedStep map coin) (foldedStep modelMap coin)
    (folded_step map tls thread schedule trusted coin) entries state

omit trusted
/-- Installing the trusted ordered iterator is exact for any accumulator,
including both leaf maps and the shared coin state. -/
theorem ordered_loop {Value InputState Acc : Type}
    (input : MapAPI Key Value InputState cmp) (inputTLS : TLSAPI Thread Slot Output)
    (law : TrustedStd input inputTLS thread schedule) (state : InputState)
    (step : Acc → Key × Value → Acc) (initial : Acc) :
    (input.entries state).foldl step initial = (input.decode state).toList.foldl step initial := by
  rw [law.btree_iter_ordered]

#print axioms fold_decode
#print axioms pair_step
#print axioms folded_step
#print axioms pair_loop
#print axioms folded_loop
#print axioms ordered_loop
end R1Z.ProverCommitLeaves43
