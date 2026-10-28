import NCE_KeyCuts
import NCE_SortCuts

set_option autoImplicit false
namespace AspisR1.NCE_KeyProducerCuts
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCE_KeyCuts

/-- ONE native zero-initializer/window, observed at an arbitrary coordinate
of the lifted16-key array. The original caller and actual split/kind remain.
Native allocation/stack and pointer association are still required. -/
def NCE_Native_KeysZero (create : Carrier → Nat → Nat → KeyState) : Prop :=
  ∀ caller batch kind, batch < 2 → kind < 3 →
    (∀ k, (create caller batch kind).keys k = 0#u64) ∧
    (create caller batch kind).caller = caller ∧
    (create caller batch kind).cursor = 0 ∧
    (create caller batch kind).batch = batch ∧ (create caller batch kind).kind = kind

theorem create_eq (create : Carrier → Nat → Nat → KeyState)
    (cut : NCE_Native_KeysZero create) (caller : Carrier) (batch kind : Nat)
    (bb : batch < 2) (kb : kind < 3) :
    create caller batch kind = ⟨caller,fun _ => 0#u64,0,batch,kind⟩ := by
  obtain ⟨cells,frame,cursor,b,k⟩ := cut caller batch kind bb kb
  have keys : (create caller batch kind).keys = fun _ => 0#u64 := funext cells
  change KeyState.mk (create caller batch kind).caller (create caller batch kind).keys
    (create caller batch kind).cursor (create caller batch kind).batch (create caller batch kind).kind = _
  congr 1 <;> first | exact frame | exact keys | exact cursor | exact b | exact k

def array (s : KeyState) : Array U64 16#usize :=
  ⟨List.ofFn (fun k : Fin 16 => s.keys k.val),by simp only [List.length_ofFn]; rfl⟩

def produce (create : Carrier → Nat → Nat → KeyState) (native : KeyState → KeyState)
    (caller : Carrier) (batch kind : Nat) : KeyState :=
  let initial := create caller batch kind
  fill native (count initial) initial

/-- The actual native zero/write recurrence constructs the full installed raw
key array, zero suffix included. No final-array or successful-sort observation
is supplied. Canonical provenance is the named NBR_/NBS_ lower dependency. -/
theorem producer (create : Carrier → Nat → Nat → KeyState)
    (zeroCut : NCE_Native_KeysZero create) (native : KeyState → KeyState)
    (writeCut : NCE_Native_KeysWrite native) (caller : Carrier) (batch kind : Nat)
    (bb : batch < 2) (kb : kind < 3)
    (queries : ∀ j, j < 22 → caller.prepared.queries.val[j]!.val < 262144) :
    array (produce create native caller batch kind) =
      Port4B_KeyInstall.keyArray caller.prepared.queries batch kind ∧
    (produce create native caller batch kind).caller = caller := by
  unfold produce
  rw [create_eq create zeroCut caller batch kind bb kb]
  dsimp only
  let initial : KeyState := ⟨caller,fun _ => 0#u64,0,batch,kind⟩
  have canon : canonical initial := queries
  have filled := fill_eq native writeCut (count initial) initial bb kb canon
    (by change 0+count initial ≤ count initial; omega)
  change array (fill native (count initial) initial) = _ ∧ (fill native (count initial) initial).caller = caller
  rw [filled]
  constructor
  · change NBI_Keys.producer caller.prepared.queries batch kind = _
    exact NBI_Keys.producer_eq _ _ _
  · rfl

/-- The constructed raw producer feeds the SAME conditional native sort.
NBJ supplies the existing frozen-position order and zero-suffix theorem. -/
theorem producer_sorted (create : Carrier → Nat → Nat → KeyState)
    (zeroCut : NCE_Native_KeysZero create) (write : KeyState → KeyState)
    (writeCut : NCE_Native_KeysWrite write) (sort : NCE_SortCuts.Step)
    (sortCut : NCE_SortCuts.NCE_Native_KeysSort sort) (caller : Carrier)
    (batch kind : Nat) (bb : batch < 2) (kb : kind < 3)
    (queries : ∀ j, j < 22 → caller.prepared.queries.val[j]!.val < 262144)
    (n : Usize) (count : n.val = (OraclePortSelectedDraft.batchPositions batch).length) :
    ∃ sorted,
      NCE_SortCuts.sort sort n.val (array (produce create write caller batch kind)) 1#usize n = ok sorted ∧
      sorted.val.take n.val =
        (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries caller.prepared.queries) batch kind).map
          (MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries caller.prepared.queries) batch kind) ∧
      sorted.val.drop n.val = List.replicate (16-n.val) 0#u64 := by
  have raw := (producer create zeroCut write writeCut caller batch kind bb kb queries).1
  obtain ⟨sorted,returned,front,suffix⟩ := NBJ_Keys.producer_sorted caller.prepared.queries batch kind n count
  have small : n.val ≤ 16 := by
    rw [count]
    unfold OraclePortSelectedDraft.batchPositions
    split <;> simp
  refine ⟨sorted,?_,front,suffix⟩
  rw [NCE_SortCuts.sort_eq sort sortCut n.val _ 1#usize n small (Nat.sub_le _ _),raw,
    ←NBI_Keys.producer_eq caller.prepared.queries batch kind]
  exact returned

#print axioms create_eq
#print axioms producer
#print axioms producer_sorted
end AspisR1.NCE_KeyProducerCuts
