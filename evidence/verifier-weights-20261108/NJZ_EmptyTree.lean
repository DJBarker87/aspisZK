import NJP_CompressionPacket
set_option autoImplicit false
noncomputable section
namespace NJZ_EmptyTree
open Aeneas Aeneas.Std Result
abbrev Digest := NJP_CompressionPacket.Digest
abbrev Table := Fin 21 → Digest

def zero : Digest := fun _ => 0#u32
def parent : Digest → Digest → Digest := NJP_CompressionPacket.model
def root : Nat → Digest
 | 0 => zero
 | n+1 => parent (root n) (root n)

def Canonical (x : Digest) := ∀ i,(x i).val<2147483647

theorem parent_canonical (left right : Digest) : Canonical (parent left right) :=
 fun _=>NJP_FieldEncoding.canonical _

theorem root_canonical (n : Nat) : Canonical (root n) := by
 cases n with
 | zero => intro i;change 0<2147483647;omega
 | succ n => exact parent_canonical _ _

/-- Native arbitrary table-window assertion: identical child arguments at
level, reply stored only at level+1, all other cells framed. -/
def StepCut (before after : Table) (level : Fin 20) (reply : Digest) : Prop :=
 ∀ j,after j=if j.val=level.val+1 then reply else before j

/-- Finite source-order chain, not kernel evaluation of twenty Poseidon calls.
Only entered children at SAME current level are instantiated with their model. -/
theorem frame (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20), StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (parent (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩))) :
 ∀ n,n≤20→∀ j : Fin 21,states n j=if j.val≤n then root j.val else zero := by
 intro n;induction n with
 | zero =>
   intro hn j
   rw [initial]
   by_cases h:j.val≤0
   · have eq:j.val=0:=by omega
     simp only [eq,root,ite_self]
   · rw [if_neg h]
 | succ n ih =>
   intro hn j
   rw [cuts n (by omega) j]
   by_cases h:j.val=n+1
   · rw [if_pos h,ih (by omega),if_pos (show n≤n from le_rfl)]
     rw [h,if_pos (show n+1≤n+1 from le_rfl)]
     rfl
   · rw [if_neg h,ih (by omega)]
     by_cases hj:j.val≤n
     · rw [if_pos hj,if_pos (by omega)]
     · rw [if_neg hj,if_neg (by omega)]

theorem roots (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20), StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (parent (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩))) :
 ∀ j,states 20 j=root j.val := by
 intro j
 simpa only [if_pos (show j.val≤20 from by omega)] using frame states initial cuts 20 (by omega) j

/-- Domain for every entered compression comes from the same preceding cuts,
not a new canonical-reply or successful-child premise. -/
theorem entered_domain (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20), StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (parent (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩)))
 (n : Fin 20) : Canonical (states n.val ⟨n.val,by omega⟩) := by
 rw [frame states initial cuts n.val (by omega) _,if_pos (show n.val≤n.val from le_rfl)]
 exact root_canonical _

structure Tree where
 next : U64
 root : Digest
 frontier : Fin 20 → Digest

def empty : Tree := ⟨0#u64,root 20,fun i=>root i.val⟩
def default : Tree := empty

/-- Empty constructor copies the exact indexed table cells and zero cursor. -/
def EmptyCut (table : Table) (out : Tree) : Prop :=
 out.next=0#u64 ∧ out.root=table ⟨20,by omega⟩ ∧
 ∀ i,out.frontier i=table ⟨i.val,by omega⟩

theorem empty_source (table : Table) (cells : ∀ i,table i=root i.val)
 (out : Tree) (cut : EmptyCut table out) : out=empty := by
 cases out with
 | mk next value frontier =>
  rcases cut with ⟨cursor,valueEq,frontierEq⟩
  simp only at cursor valueEq frontierEq
  subst next
  rw [cells] at valueEq
  subst value
  have fs : frontier=(fun i : Fin 20=>root i.val) := by
   funext i;rw [frontierEq,cells]
  rw [fs]
  rfl

/-- Compose the empty constructor with its CLOSED-candidate child chain;
the table equality and every entered child domain are internally derived. -/
theorem empty_root (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20), StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (parent (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩)))
 (out : Tree) (constructor : EmptyCut (states 20) out) :
 out=empty ∧ ∀ n : Fin 20,Canonical (states n.val ⟨n.val,by omega⟩) :=
 ⟨empty_source _ (roots states initial cuts) out constructor,
  entered_domain states initial cuts⟩

/-- Default's sole child reply is returned unchanged, on every field. -/
def DefaultCut (reply out : Tree) : Prop := out=reply

theorem default_root (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20), StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (parent (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩)))
 (child out : Tree) (constructor : EmptyCut (states 20) child)
 (returnCut : DefaultCut child out) : out=default := by
 have childResult := (empty_root states initial cuts child constructor).1
 exact returnCut.trans childResult

#print axioms parent_canonical
#print axioms root_canonical
#print axioms frame
#print axioms roots
#print axioms entered_domain
#print axioms empty_source
#print axioms empty_root
#print axioms default_root
end NJZ_EmptyTree
