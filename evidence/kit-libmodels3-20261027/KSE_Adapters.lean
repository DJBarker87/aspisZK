import KSE_Interval
set_option autoImplicit false
namespace KSE
/-- A borrow token retains its logical slot and explicit final-value writeback.
Consume each continuation once, at the end of that borrow's lifetime. -/
def borrow {T : Type} (back : Bool) (s : Cursor T) :
    Option (Nat × T) × Cursor T × (Cursor T → Option T → Cursor T) :=
  match takeSlot back s with
  | none => (none,s,fun t _ => t)
  | some (i,t) => (some (i,s.mem i),t,fun u v =>
      match v with
      | none => u
      | some x => {u with mem := write u.mem i x})

def reverseNext {T : Type} := @borrow T true
/-- Pair projection is for read-only uses. Mutable callers must keep borrow.2.2. -/
def nextBackPair {T : Type} (s : Cursor T) := ((reverseNext s).1, (reverseNext s).2.1)

def enumerateNext {T : Type} (count : Nat) (s : Cursor T) :=
  let (v,t,restore) := borrow false s
  (v.map (fun p => (count,p)), (if v.isSome then count+1 else count), t, restore)

theorem borrow_writeback {T : Type} (d : Bool) (s t u : Cursor T) (i : Nat) (x : T)
    (h : takeSlot d s = some (i,t)) :
    (borrow d s).2.2 u (some x) = {u with mem := write u.mem i x} := by
  simp [borrow, h]

theorem borrow_keeps_bounds {T : Type} (d : Bool) (s t u : Cursor T) (i : Nat) (x : T)
    (h : takeSlot d s = some (i,t)) :
    ((borrow d s).2.2 u (some x)).lo = u.lo ∧
      ((borrow d s).2.2 u (some x)).hi = u.hi := by
  rw [borrow_writeback d s t u i x h]
  exact ⟨rfl,rfl⟩

theorem reverse_is_back {T : Type} (s : Cursor T) : reverseNext s = borrow true s := rfl

theorem enumerate_restoration {T : Type} (n : Nat) (s : Cursor T) :
    (enumerateNext n s).2.2.2 = (borrow false s).2.2 := rfl

/-- Exact mutable chunks are disjoint logical blocks. The short tail is held
outside the iterator, never yielded, and is restored unchanged. Width must be
positive; zero width is a Rust panic, not a zero-sized chunk iterator. -/
def chunkCursor {T : Type} (xs : List T) (width : Nat) : Cursor (List T) :=
  ⟨0,xs.length / width,fun k => (xs.drop (k*width)).take width⟩

def chunkRemainder {T : Type} (xs : List T) (width : Nat) :=
  xs.drop ((xs.length / width)*width)

def restoredChunks {T : Type} (xs : List T) (width : Nat)
    (f : Nat → List T → List T) (ds : List Bool) : List T :=
  (snapshot (xs.length / width) (run f ds (chunkCursor xs width)).1.mem).flatten ++
    chunkRemainder xs width

/-- Callers must preserve the length of each borrowed chunk. This theorem
records restoration for arbitrary replacement lists; legal Rust writes are
its length-preserving instances. -/
theorem chunks_restoration {T : Type} (xs : List T) (w : Nat)
    (f : Nat → List T → List T) (ds : List Bool) :
    restoredChunks xs w f ds =
      (snapshot (xs.length / w)
        (applyWrites (chunkCursor xs w).mem (run f ds (chunkCursor xs w)).2)).flatten ++
          chunkRemainder xs w := by
  unfold restoredChunks
  rw [restoration]

theorem chunks_no_duplicate_yields {T : Type} (xs : List T) (w : Nat)
    (f : Nat → List T → List T) (ds : List Bool) :
    ((run f ds (chunkCursor xs w)).2.map Prod.fst).Nodup :=
  no_duplicate_yields f ds _

/-- Distinct chunks cannot alias an element, including mixed front/back use. -/
theorem chunk_slots_disjoint (w k l i j : Nat) (hw : 0 < w)
    (hi : i < w) (hj : j < w) (hne : k ≠ l) : k*w+i ≠ l*w+j := by
  intro eq
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have le : (k+1)*w ≤ l*w := Nat.mul_le_mul_right w h
    rw [Nat.add_mul, Nat.one_mul] at le
    omega
  · have le : (l+1)*w ≤ k*w := Nat.mul_le_mul_right w h
    rw [Nat.add_mul, Nat.one_mul] at le
    omega

/-- Windows overlap and are shared. There is deliberately no mutable-windows
iterator: representing overlapping windows as exclusive slots would be false. -/
def window {T : Type} (xs : List T) (index width : Nat) := (xs.drop index).take width

def windowNext {T : Type} (xs : List T) (index width : Nat) :
    Option (List T) × Nat :=
  if index + width ≤ xs.length then (some (window xs index width), index+1)
  else (none,index)

theorem window_keeps_source {T : Type} (xs : List T) (i w : Nat) :
    window xs i w = (xs.drop i).take w := rfl

#print axioms borrow_writeback
#print axioms borrow_keeps_bounds
#print axioms reverse_is_back
#print axioms enumerate_restoration
#print axioms chunks_restoration
#print axioms chunks_no_duplicate_yields
#print axioms chunk_slots_disjoint
#print axioms window_keeps_source
end KSE
