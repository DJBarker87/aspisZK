import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Growth
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations
/-- Snapshot copying includes the old initialized prefix, never reading newly
allocated spare bytes. The primitive reserve family supplies allocation outcome. -/
def grownCell (old : Cell) (newSize newCap : Nat) : Cell :=
 {old with size := newSize, capacity := newCap,
   contents := fun i => if i<old.size then old.contents i else none}

def relocate (m : Memory) (old : Token) (c : Cell) (p newSize newCap : Nat) : Memory :=
 let generation := m.generations p+1
 let fresh := Token.mk p generation
 {m with heap := put (put m.heap old.address (some {c with live := false})) p
             (some (grownCell c newSize newCap))
         generations := fun a => if a=p then generation else m.generations a
         slots := fun s => if s=c.owner then some fresh else m.slots s}

def growHeader {T : Type} (v : Vector T) (t : Token) (newCap : Nat) : Vector T :=
 {v with token := t, capacity := newCap}

theorem prefix (c : Cell) (newSize newCap i : Nat) (h:i<c.size) :
 (grownCell c newSize newCap).contents i=c.contents i := by simp [grownCell,h]
theorem spare (c : Cell) (newSize newCap i : Nat) (h:c.size≤i) :
 (grownCell c newSize newCap).contents i=none := by
 simp [grownCell,show ¬i<c.size by omega]
theorem typed_prefix {T : Type} (k : Codec T) (c : Cell) (newSize newCap s : Nat) (v : T)
 (grow:c.size≤newSize) (h:Represents k c s v) : Represents k (grownCell c newSize newCap) s v := by
 refine ⟨?_,?_⟩
 · exact Nat.le_trans h.1 grow
 · intro i hi
   rw [prefix c newSize newCap (s+i) (by have hh:=h.1; unfold Fits at hh; omega)]
   exact h.2 i hi

theorem same_address_live (m : Memory) (t : Token) (c : Cell) (n cap : Nat) :
 (relocate m t c t.address n cap).heap t.address=some (grownCell c n cap) := put_same _ _ _

theorem distinct_address_dead (m : Memory) (t : Token) (c : Cell) (p n cap : Nat) (h:t.address≠p) :
 (relocate m t c p n cap).heap t.address=some {c with live := false} := by
 rw [show (relocate m t c p n cap).heap t.address=
   put (put m.heap t.address (some {c with live := false})) p (some (grownCell c n cap)) t.address by rfl]
 rw [put_other _ _ _ _ h,put_same]

theorem stale_generation (m : Memory) (t : Token) (c : Cell) (n cap : Nat)
 (generation:m.generations t.address=t.generation) :
 (relocate m t c t.address n cap).generations t.address≠t.generation := by
 simp only [relocate,ite_true]
 omega
#print axioms prefix
#print axioms spare
#print axioms typed_prefix
#print axioms same_address_live
#print axioms distinct_address_dead
#print axioms stale_generation
end R1Z.PV_OWN_Growth
