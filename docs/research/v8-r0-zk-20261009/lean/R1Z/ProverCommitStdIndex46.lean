import R1Z.ProverCommitTrustedStd24
/-! D157 pure collection observer used in ProgrammedTree::multiproof. This extends the
named TrustedStd boundary for BTreeMap's Index operation. It does not add a
source callback, interior-mutability, allocation-totality or privacy law. -/
set_option autoImplicit false
namespace R1Z.ProverCommitStdIndex46
open Aeneas.Std ProverCommitTrustedStd24
variable {Key Value Table Thread Slot Output : Type}
variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

def indexModel (map : Std.TreeMap Key Value cmp) (key : Key) : Result Value :=
  match map[key]? with
  | some value => .ok value
  | none => .fail .panic

/-- Documented std indexing semantics: return the associated value; panic
when the key is absent. Only a shared immutable value is returned here. -/
structure TrustedIndex (api : MapAPI Key Value Table cmp)
    (index : Table → Key → Result Value) : Prop where
  btree_index : ∀ table key, index table key = indexModel (api.decode table) key

variable (api : MapAPI Key Value Table cmp) (index : Table → Key → Result Value)
    (law : TrustedIndex api index)
include law

theorem index_found (table : Table) (key : Key) (value : Value)
    (found : (api.decode table)[key]? = some value) : index table key = .ok value := by
  rw [law.btree_index,indexModel,found]

theorem index_absent (table : Table) (key : Key)
    (absent : (api.decode table)[key]? = none) : index table key = .fail .panic := by
  rw [law.btree_index,indexModel,absent]

omit law
/-- Consistency witness for the extension, not a verification of std internals. -/
theorem model_consistent :
    TrustedIndex (modelMap (Key := Key) (Value := Value) (cmp := cmp)) indexModel := ⟨fun _ _ => rfl⟩

/-- D157's pure Vec::Index observer, used at the same callback. The model
records the panic branch; no allocation success or unbounded indexing claim. -/
def sequenceIndex {V : Type} (xs : List V) (i : Nat) : Result V :=
  match xs[i]? with
  | some value => .ok value
  | none => .fail .panic

structure TrustedSequence {V Seq : Type} (decode : Seq → List V)
    (index : Seq → Nat → Result V) : Prop where
  vec_index : ∀ xs i, index xs i = sequenceIndex (decode xs) i

theorem sequence_found {V Seq : Type} (decode : Seq → List V)
    (index : Seq → Nat → Result V) (std : TrustedSequence decode index)
    (xs : Seq) (i : Nat) (v : V) (found : (decode xs)[i]?=some v) :
    index xs i = .ok v := by
  rw [std.vec_index,sequenceIndex,found]

theorem sequence_model_consistent {V : Type} :
    TrustedSequence (id : List V → List V) sequenceIndex := ⟨fun _ _ => rfl⟩

#print axioms sequence_found
#print axioms sequence_model_consistent
#print axioms index_found
#print axioms index_absent
#print axioms model_consistent
end R1Z.ProverCommitStdIndex46
