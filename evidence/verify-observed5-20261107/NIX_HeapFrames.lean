import Aeneas
set_option autoImplicit false
namespace AspisR1.NIX_HeapFrames
/-- The native one-row store in NIX_claims_heap, transcribed as a finite update. -/
def write {Row : Type} (state : Fin 3 → Option Row) (p : Fin 3) (row : Row) :
 Fin 3 → Option Row := fun j=>if j=p then some row else state j
/-- Arbitrary pre-state and decoder replies; no zero initialization assumption. -/
def prefixRows {Row : Type} (before : Fin 3 → Option Row) (rows : Fin 3 → Row)
 (n : Nat) : Fin 3 → Option Row := fun j => if j.val<n then some (rows j) else before j

theorem initial {Row : Type} (before : Fin 3 → Option Row) (rows : Fin 3 → Row) :
 prefixRows before rows 0=before := by funext j;simp [prefixRows]

theorem one_write {Row : Type} (before : Fin 3 → Option Row) (rows : Fin 3 → Row) (p : Fin 3) :
 write (prefixRows before rows p.val) p (rows p)=prefixRows before rows (p.val+1) := by
 funext j
 by_cases same : j=p
 · subst j;simp [write,prefixRows]
 · have different : j.val≠p.val := fun h=>same (Fin.ext h)
   simp only [write,if_neg same,prefixRows]
   by_cases lower : j.val<p.val
   · rw [if_pos lower,if_pos (by omega)]
   · rw [if_neg lower,if_neg (by omega)]

theorem completed {Row : Type} (before : Fin 3 → Option Row) (rows : Fin 3 → Row) :
 prefixRows before rows 3=fun j=>some (rows j) := by
 funext j;exact if_pos j.isLt

/-- Logical allocation ledger. Freed payload is absent, never read as a value. -/
structure Heap (Row : Type) where
 live : Nat → Bool
 payload : Nat → Option (Fin 3 → Option Row)
 metadata : Nat → Nat

def allocate {Row : Type} (h : Heap Row) (a : Nat) : Heap Row where
 live := fun b=>if b=a then true else h.live b
 payload := fun b=>if b=a then some (fun _=>none) else h.payload b
 metadata := h.metadata

def release {Row : Type} (h : Heap Row) (a : Nat) : Heap Row where
 live := fun b=>if b=a then false else h.live b
 payload := fun b=>if b=a then none else h.payload b
 metadata := h.metadata

def initialized {Row : Type} (h : Heap Row) (a : Nat) (rows : Fin 3 → Row) (n : Nat) : Heap Row :=
 {allocate h a with payload:=fun b=>if b=a then some (prefixRows (fun _=>none) rows n) else h.payload b}

def Frame {Row : Type} (before after : Heap Row) (a : Nat) : Prop :=
 (∀ b,b≠a → after.live b=before.live b ∧ after.payload b=before.payload b) ∧
 after.metadata=before.metadata

theorem allocated_frame {Row : Type} (h : Heap Row) (a : Nat) : Frame h (allocate h a) a := by
 refine ⟨?_,rfl⟩;intro b different;simp [allocate,different]

theorem initialized_frame {Row : Type} (h : Heap Row) (a : Nat) (rows : Fin 3 → Row) (n : Nat) :
 Frame h (initialized h a rows n) a := by
 refine ⟨?_,rfl⟩;intro b different;simp [initialized,allocate,different]

/-- Uniform in every abort prefix n, including zero rows and all three rows.
This is the safe ledger law, not a claim that the native deallocator has been bridged. -/
theorem abort_prefix {Row : Type} (h : Heap Row) (a : Nat) (rows : Fin 3 → Row) (n : Nat) :
 Frame h (release (initialized h a rows n) a) a ∧
 (release (initialized h a rows n) a).live a=false ∧
 (release (initialized h a rows n) a).payload a=none := by
 refine ⟨⟨?_,rfl⟩,?_,?_⟩
 · intro b different;simp [release,initialized,allocate,different]
 · simp [release]
 · simp [release]

/-- Injectivity and bounds of the actual [QM31;29] row address window. -/
theorem window (p q : Fin 3) (i j : Fin 29) :
 29*p.val+i.val<87 ∧ (29*p.val+i.val=29*q.val+j.val ↔ p=q ∧ i=j) := by
 constructor
 · omega
 · constructor
   · intro same
     have rows : p.val=q.val := by omega
     exact ⟨Fin.ext rows,Fin.ext (by omega)⟩
   · rintro ⟨rfl,rfl⟩;rfl

#print axioms initial
#print axioms one_write
#print axioms completed
#print axioms allocated_frame
#print axioms initialized_frame
#print axioms abort_prefix
#print axioms window
end AspisR1.NIX_HeapFrames
