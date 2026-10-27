import Std.Data.TreeMap.Lemmas
import R1Z.ProverCommitTablePrefix21
/-! Universal Lean Std.TreeMap transport to the retained list-table model.
This is a standard-library model theorem, not an identification of the
Rust allocator/tree implementation with Lean's tree representation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTreeMap22
open ProverCommitTable20
variable {Key Value : Type} [DecidableEq Key] [DecidableEq Value]

/-- Membership graph suffices even without an explicit uniqueness premise:
all duplicate keys, if present, necessarily carry the same value. -/
theorem lookup_of_graph (entries : List (Key × Value)) (key : Key) (value : Option Value)
    (graph : ∀ v, (key,v) ∈ entries ↔ value = some v) : lookup entries key = value := by
  induction entries with
  | nil =>
    cases value with
    | none => rfl
    | some v => exact False.elim (List.not_mem_nil ((graph v).mpr rfl))
  | cons entry tail ih =>
    rcases entry with ⟨a,b⟩
    by_cases same : a=key
    · subst a
      have hv := (graph b).mp (List.mem_cons_self ..)
      simp only [lookup,ite_true]
      exact hv.symm
    · simp only [lookup,if_neg same]
      apply ih
      intro v
      rw [← graph v]
      simp only [List.mem_cons,Prod.mk.injEq]
      constructor
      · exact Or.inr
      · rintro (⟨he,_⟩ | ht)
        · exact False.elim (same he.symm)
        · exact ht

variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

theorem lookup_toList (tree : Std.TreeMap Key Value cmp) (key : Key) :
    lookup tree.toList key = tree[key]? := by
  exact lookup_of_graph _ _ _ (fun v => Std.TreeMap.mem_toList_iff_getElem?_eq_some)

/-- Every finite tree size and every key; insert, overwrite and miss all
have the identical observable lookup law. -/
theorem insert_lookup (tree : Std.TreeMap Key Value cmp) (key query : Key) (answer : Value) :
    lookup (tree.insert key answer).toList query =
      lookup (ProverCommitTable20.insert tree.toList key answer false).1 query := by
  rw [lookup_toList,Std.TreeMap.getElem?_insert,ProverCommitTable20.insert_lookup,lookup_toList]
  simp only [Std.LawfulEqCmp.compare_eq_iff_eq]

def program (tree : Std.TreeMap Key Value cmp) (key : Key) (answer : Value) (collision : Bool) :
    Std.TreeMap Key Value cmp × Bool :=
  (tree.insert key answer, collision || conflict tree[key]? answer)

theorem program_collision (tree : Std.TreeMap Key Value cmp) (key : Key)
    (answer : Value) (collision : Bool) :
    (program tree key answer collision).2 =
      (ProverCommitTable20.insert tree.toList key answer collision).2 := by
  rw [ProverCommitTable20.insert_collision,lookup_toList]
  rfl

/-- Enumeration preserves exactly the published key/value graph. -/
theorem enumerated (tree : Std.TreeMap Key Value cmp) (key : Key) (value : Value) :
    (key,value) ∈ tree.toList ↔ lookup tree.toList key = some value := by
  rw [lookup_toList]
  exact Std.TreeMap.mem_toList_iff_getElem?_eq_some

def writes (tree : Std.TreeMap Key Value cmp) (collision : Bool) :
    List (Key × Value) → Std.TreeMap Key Value cmp × Bool
  | [] => (tree,collision)
  | (key,answer)::tail =>
      let next := program tree key answer collision
      writes next.1 next.2 tail

/-- Extensional table relation and sticky collision are preserved over every
finite source write schedule, including repeated keys and arbitrary prefixes. -/
theorem writes_transport (entries table : List (Key × Value))
    (tree : Std.TreeMap Key Value cmp) (collision : Bool)
    (related : ∀ key, lookup table key = tree[key]?) :
    (∀ query, lookup (ProverCommitTable20.writes table collision entries).1 query =
      (writes tree collision entries).1[query]?) ∧
    (ProverCommitTable20.writes table collision entries).2 =
      (writes tree collision entries).2 := by
  induction entries generalizing tree table collision with
  | nil => exact ⟨related,rfl⟩
  | cons entry tail ih =>
    rcases entry with ⟨key,answer⟩
    have rel : ∀ query, lookup (ProverCommitTable20.insert table key answer collision).1 query =
        (tree.insert key answer)[query]? := by
      intro query
      rw [ProverCommitTable20.insert_lookup,Std.TreeMap.getElem?_insert,related]
      simp only [Std.LawfulEqCmp.compare_eq_iff_eq]
    have flag : (ProverCommitTable20.insert table key answer collision).2 =
        (collision || conflict tree[key]? answer) := by
      rw [ProverCommitTable20.insert_collision,related]
    simpa only [writes,program,ProverCommitTable20.writes,flag] using
      ih (ProverCommitTable20.insert table key answer collision).1
        (tree.insert key answer) (collision || conflict tree[key]? answer) rel

theorem enumeration_order (tree : Std.TreeMap Key Value cmp) :
    tree.toList.Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  Std.TreeMap.ordered_keys_toList

#print axioms writes_transport
#print axioms enumeration_order

#print axioms lookup_of_graph
#print axioms lookup_toList
#print axioms insert_lookup
#print axioms program_collision
#print axioms enumerated
end R1Z.ProverCommitTreeMap22
