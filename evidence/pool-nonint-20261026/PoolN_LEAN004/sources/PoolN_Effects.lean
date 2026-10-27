import PoolN_Guards
set_option autoImplicit false
namespace AspisR1.PoolN_Effects
open PoolN_Guards

/-- The error and prior effect prefix are retained. This is an operational
composition lemma, not an assumption that an entire Pool call frames a key. -/
structure Outcome (State Event Value : Type) where
  result : Except Error Value
  state : State
  effects : List Event

def afterGuard {S E V : Type} (check : Except Error Unit) (state : S)
    (prefix : List E) (next : S → List E → Outcome S E V) : Outcome S E V :=
  match check with
  | .error err => ⟨.error err,state,prefix⟩
  | .ok () => next state prefix

theorem rejected_prefix {S E V : Type} (check : Except Error Unit) (err : Error)
    (state : S) (prefix : List E) (next : S → List E → Outcome S E V)
    (rejected : check = .error err) :
    afterGuard check state prefix next = ⟨.error err,state,prefix⟩ := by
  rw [rejected]
  rfl

/-- Any prior effects remain in exactly their original order, and the suffix
(including close/reassign/realloc/CPI operations) is not executed. -/
theorem prepared_prefix {S E V : Type} (a : Account) (id : Key) (size : Nat)
    (cp : CheckpointLength a) (plan : size = 10000 ∨ size = 8504)
    (state : S) (prefix : List E) (next : S → List E → Outcome S E V) :
    afterGuard (prepared a id size) state prefix next =
      ⟨.error .InvalidAccountData,state,prefix⟩ :=
  rejected_prefix _ _ state prefix next (prepared_rejects a id size cp plan)

/-- Read-only wrapper state equality frames every projection, not just data.
The caller must supply the actual checked equality; this lemma supplies no
runtime admission or missing handler law. -/
theorem project_frame {S V : Type} (before after : S) (read : S → V)
    (unchanged : after = before) : read after = read before := by
  rw [unchanged]

#print axioms rejected_prefix
#print axioms prepared_prefix
#print axioms project_frame
end AspisR1.PoolN_Effects
