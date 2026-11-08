import PV_LIB_A_OwnerStoreV2
import PV_LIB_A_WriterNumbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StoreCounterV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_A_StorePrimitiveV2
/-- Local source effects preserve the unused activation counter. This says
nothing about equality across a summary/expanded callee boundary (D961). -/
def Counter (s : Store Data) (out : Option (Store Data)) : Prop :=
  ∀ t, out = some t → t.nextActivation = s.nextActivation

theorem none_counter (s : Store Data) : Counter s none := by
  intro t impossible
  cases impossible

theorem same_counter (s : Store Data) : Counter s (some s) := by
  intro t eq
  cases eq
  rfl

theorem read_bind {A : Type} (s : Store Data) (x : Option A)
    (f : A → Option (Store Data)) (h : ∀ a, Counter s (f a)) : Counter s (x.bind f) := by
  cases x with
  | none => exact none_counter s
  | some a => exact h a

theorem store_bind (s : Store Data) (x : Option (Store Data))
    (f : Store Data → Option (Store Data))
    (first : Counter s x) (second : ∀ t, Counter t (f t)) : Counter s (x.bind f) := by
  cases h : x with
  | none => exact none_counter s
  | some t =>
    intro u eq
    exact (second t u eq).trans (first t h)

theorem write_counter (C : Carrier OWNER Data) (s : Store Data) (p : Address) (v : Option Data) :
    Counter s (writeAddress C s p v) := by
  intro t eq
  exact PV_LIB_A_WriterNumbering.write_counter C s t p v eq

theorem put_counter (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (ref : Data) (fields : List Nat) (v : Data) : Counter s (put C s w ref fields v) := by
  unfold put
  apply read_bind
  intro p
  exact write_counter C s p (some v)

theorem modify_counter (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (ref : Data) (fields : List Nat) (f : Nat → Nat) : Counter s (modifyNumber C s w ref fields f) := by
  unfold modifyNumber
  apply read_bind
  intro p
  apply read_bind
  intro n
  exact write_counter C s p (some (.number (f n)))

theorem primitive_counter (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (args : List Data) :
    Counter s (PV_THR2_LibrarySemantics_FetchAdd351 C args s w) ∧
    Counter s (PV_THR2_LibrarySemantics_FetchSub581 C args s w) ∧
    Counter s (PV_THR2_LibrarySemantics_AtomicStore557 C args s w) ∧
    Counter s (PV_THR2_LibrarySemantics_MemReplace442 C args s w) ∧
    Counter s (PV_THR2_LibrarySemantics_PtrWrite308 C args s w) ∧
    Counter s (PV_THR2_LibrarySemantics_PtrWrite364 C args s w) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · unfold PV_THR2_LibrarySemantics_FetchAdd351
    split
    · exact modify_counter _ _ _ _ _ _
    · exact none_counter s
  · unfold PV_THR2_LibrarySemantics_FetchSub581
    split
    · exact modify_counter _ _ _ _ _ _
    · exact none_counter s
  · unfold PV_THR2_LibrarySemantics_AtomicStore557
    split
    · exact put_counter _ _ _ _ _ _
    · exact none_counter s
  · unfold PV_THR2_LibrarySemantics_MemReplace442
    split
    · exact put_counter _ _ _ _ _ _
    · exact none_counter s
  · unfold PV_THR2_LibrarySemantics_PtrWrite308
    split
    · exact put_counter _ _ _ _ _ _
    · exact none_counter s
  · unfold PV_THR2_LibrarySemantics_PtrWrite364
    split
    · exact put_counter _ _ _ _ _ _
    · exact none_counter s

theorem cas_counter {E : Type} (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (args : List Data) (r : Reply OWNER E Data) :
    Counter s (PV_LIB_A_StoreAtomicV2.compareExchange C args s w r) := by
  unfold PV_LIB_A_StoreAtomicV2.compareExchange
  split
  · split
    · apply read_bind
      intro variant
      split
      · exact put_counter _ _ _ _ _ _
      · exact same_counter s
      · exact none_counter s
    · exact none_counter s
  · exact same_counter s

theorem new_actions_counter (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (f : PV_LIB_A_StoreDispatchV2.Function) (args : List Data)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    Counter s (PV_LIB_A_StoreDispatchV2.interpret C f args s w r) := by
  cases f with
  | arcClone360 =>
    simp only [PV_LIB_A_StoreDispatchV2.interpret]
    unfold PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360
    apply read_bind
    intro p
    apply read_bind
    intro n
    exact write_counter _ _ _ _
  | fetchAdd351 => exact (primitive_counter C s w args).1
  | fetchSub581 => exact (primitive_counter C s w args).2.1
  | store557 => exact (primitive_counter C s w args).2.2.1
  | memReplace442 => exact (primitive_counter C s w args).2.2.2.1
  | ptrWrite308 => exact (primitive_counter C s w args).2.2.2.2.1
  | ptrWrite364 => exact (primitive_counter C s w args).2.2.2.2.2
  | boolStore646 =>
    simp only [PV_LIB_A_StoreDispatchV2.interpret]
    unfold PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_AtomicBoolStore646
    split
    · exact put_counter _ _ _ _ _ _
    · exact none_counter s
  | cellSet504 =>
    simp only [PV_LIB_A_StoreDispatchV2.interpret]
    unfold PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CellSet504
    split
    · exact put_counter _ _ _ _ _ _
    · exact none_counter s
  | cas530 => exact cas_counter C s w args r
  | cas555 => exact cas_counter C s w args r

theorem scope_actions_counter (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (f : PV_LIB_A_ScopeDispatchV2.Function) (args : List Data) :
    Counter s (PV_LIB_A_ScopeDispatchV2.interpret C f args s w) := by
  cases f with
  | increment457 =>
    simp only [PV_LIB_A_ScopeDispatchV2.interpret]
    unfold PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457
    split
    · exact modify_counter _ _ _ _ _ _
    · exact none_counter s
  | decrement611 =>
    simp only [PV_LIB_A_ScopeDispatchV2.interpret]
    unfold PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeDecrement611
    split
    · split
      · apply store_bind
        · exact put_counter _ _ _ _ _ _
        · intro t
          exact modify_counter _ _ _ _ _ _
      · exact modify_counter _ _ _ _ _ _
    · exact none_counter s

theorem celltake_counter (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (args : List Data) :
    Counter s (PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641 C args s w) := by
  unfold PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641
  split
  · apply read_bind
    intro p
    apply read_bind
    intro old
    apply read_bind
    intro empty
    exact write_counter _ _ _ _
  · exact none_counter s

/-- Reuse the slice invariant by NAME after any new source-store action.
This is a local invariant lemma; complete native administration and the full
OwnInit history still need their own composition. -/
theorem numbered_after_action (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (f : PV_LIB_A_StoreDispatchV2.Function) (args : List Data)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) (c : Config) (t : Store Data)
    (sameStore : c.store = s) (numbered : PV_STX2_LiveNumbering.Numbered c)
    (changed : PV_LIB_A_StoreDispatchV2.interpret C f args s w r = some t) :
    PV_STX2_LiveNumbering.Numbered {c with store := t} := by
  apply PV_LIB_A_WriterNumbering.local_store c t numbered
  have equal := new_actions_counter C s w f args r t changed
  simpa only [sameStore,equal] using (Nat.le_refl s.nextActivation)

#print axioms none_counter
#print axioms same_counter
#print axioms read_bind
#print axioms store_bind
#print axioms write_counter
#print axioms put_counter
#print axioms modify_counter
#print axioms primitive_counter
#print axioms cas_counter
#print axioms new_actions_counter
#print axioms scope_actions_counter
#print axioms celltake_counter
#print axioms numbered_after_action
end PV_LIB_A_StoreCounterV2
