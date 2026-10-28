import R1Z.ProverCommitTrustedStd24
/-! First-conflict transcript publication. A rejected merge returns no table;
the source has already overwritten its local entry, then discards the attempt.
It is not the Merkle programming callback's sticky-collision loop. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMerge33
open ProverCommitTrustedStd24
variable {Key Value State Thread Slot Output : Type}
variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
variable [DecidableEq Value]

def step (map : MapAPI Key Value State cmp) (s : State) (entry : Key × Value) : Option State :=
  let next := map.insert s entry.1 entry.2
  match next.2 with
  | none => some next.1
  | some old => if old = entry.2 then some next.1 else none

def recursive (map : MapAPI Key Value State cmp) : List (Key × Value) → State → Option State
  | [], s => some s
  | entry::tail, s => (step map s entry).bind (recursive map tail)

def loop (map : MapAPI Key Value State cmp) (entries : List (Key × Value))
    (s : State) : Option State :=
  entries.foldl (fun acc entry => acc.bind (fun state => step map state entry)) (some s)

theorem loop_recursive (map : MapAPI Key Value State cmp)
    (entries : List (Key × Value)) (s : State) : loop map entries s = recursive map entries s := by
  have aux : ∀ entries (initial : Option State),
      entries.foldl (fun acc entry => acc.bind (fun state => step map state entry)) initial =
        initial.bind (recursive map entries) := by
    intro entries
    induction entries with
    | nil => intro initial; cases initial <;> rfl
    | cons entry tail ih =>
      intro initial
      cases initial with
      | none => simpa only [List.foldl_cons,Option.bind_none] using ih none
      | some state =>
        simp only [List.foldl_cons,Option.bind_some,ih,recursive]
  exact aux entries (some s)

variable [DecidableEq Thread]
variable (map : MapAPI Key Value State cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (trusted : TrustedStd map tls thread schedule)
include trusted

theorem step_decode (s : State) (entry : Key × Value) :
    (step map s entry).map map.decode = step modelMap (map.decode s) entry := by
  simp only [step,trusted.btree_insert_previous,modelMap,ProverCommitTreeOps23.treeInsert]
  cases found : (map.decode s)[entry.1]? with
  | none => simp only [Option.map_some,trusted.btree_insert_state]
  | some old =>
    by_cases equal : old = entry.2
    · simp only [if_pos equal,Option.map_some,trusted.btree_insert_state]
    · simp only [if_neg equal,Option.map_none]

/-- Arbitrary ordered transcript inputs, keys and table sizes. Both failure
and successful exact final state pass through the two existing insert fields. -/
theorem recursive_decode (entries : List (Key × Value)) (s : State) :
    (recursive map entries s).map map.decode = recursive modelMap entries (map.decode s) := by
  induction entries generalizing s with
  | nil => rfl
  | cons entry tail ih =>
    have hs := step_decode map tls thread schedule trusted s entry
    simp only [recursive]
    cases found : step map s entry with
    | none =>
      simp only [found,Option.map_none] at hs
      rw [← hs]
      rfl
    | some next =>
      simp only [found,Option.map_some] at hs
      rw [← hs]
      exact ih next

theorem native_ordered_loop_decode (s transcript : State) :
    (loop map (map.entries transcript) s).map map.decode =
      recursive modelMap (map.decode transcript).toList (map.decode s) := by
  rw [loop_recursive,recursive_decode map tls thread schedule trusted,
    trusted.btree_iter_ordered]

#print axioms loop_recursive
#print axioms step_decode
#print axioms recursive_decode
#print axioms native_ordered_loop_decode
end R1Z.ProverCommitMerge33
