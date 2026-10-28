import R1Z.PV_W_Enriched
set_option autoImplicit false
namespace R1Z.PV_OWN_Heap
abbrev Cell := PV_W_Enriched.Allocation
abbrev Heap := Nat → Option Cell
structure Token where
  address : Nat
  generation : Nat
  deriving DecidableEq
structure Loan where
  token : Token
  borrower : Nat
  exclusive : Bool
  deriving DecidableEq
structure Memory where
  heap : Heap
  generations : Nat → Nat
  slots : Nat → Option Token
  loans : List Loan

def put (h : Heap) (p : Nat) (c : Option Cell) : Heap :=
  fun a => if a=p then c else h a

def Live (m : Memory) (t : Token) (c : Cell) : Prop :=
  m.heap t.address=some c ∧ c.live=true ∧ m.generations t.address=t.generation

def Disjoint (p : Nat) (a : Cell) (q : Nat) (b : Cell) : Prop :=
  p+a.size≤q ∨ q+b.size≤p

def Valid (h : Heap) : Prop :=
  (∀ p c, h p=some c → c.live=true → p≠0 ∧ c.alignment>0 ∧ p%c.alignment=0) ∧
  (∀ p q a b, h p=some a → h q=some b → a.live=true → b.live=true → p≠q → Disjoint p a q b)

def NoLoans (m : Memory) (t : Token) : Prop := ∀ l ∈ m.loans, l.token≠t

def Owned (m : Memory) (slot : Nat) (t : Token) (c : Cell) : Prop :=
  Live m t c ∧ m.slots slot=some t ∧ c.owner=slot

def Writable (m : Memory) (slot : Nat) (t : Token) (c : Cell) : Prop :=
  Owned m slot t c ∧ NoLoans m t

def emptyCell (size alignment owner : Nat) : Cell :=
  ⟨size,alignment,0,fun _ => none,owner,true⟩

theorem put_same (h : Heap) (p : Nat) (c : Option Cell) : put h p c p=c := by simp [put]
theorem put_other (h : Heap) (p a : Nat) (c : Option Cell) (hne : a≠p) :
    put h p c a=h a := by simp [put,hne]
theorem put_shadow (h : Heap) (p : Nat) (a b : Option Cell) :
    put (put h p a) p b=put h p b := by funext q; by_cases hq:q=p <;> simp [put,hq]
theorem put_commute (h : Heap) (p q : Nat) (a b : Option Cell) (hne:p≠q) :
    put (put h p a) q b=put (put h q b) p a := by
  funext r; by_cases hp:r=p <;> by_cases hq:r=q <;> simp_all [put]
#print axioms put_same
#print axioms put_other
#print axioms put_shadow
#print axioms put_commute
end R1Z.PV_OWN_Heap
