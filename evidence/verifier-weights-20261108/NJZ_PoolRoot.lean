import NJZ_TreeParent
set_option autoImplicit false
noncomputable section
namespace NJZ_PoolRoot
open Aeneas Aeneas.Std Result
open NJZ_EmptyTree

/-- CLOSED child's encoded permutation reply is canonical on every model seed.
Its native application still requires canonical actual left/right inputs. -/
theorem reply_canonical (left right : Digest) :
 Canonical (NJZ_TreeParent.reply left right) := fun _=>NJP_FieldEncoding.canonical _

/-- Exact native initialization/step cuts establish each entered child domain
on the SAME table, before the child is applied. No child-success premise. -/
theorem domains (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20),StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (NJZ_TreeParent.reply (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩))) :
 ∀ n,n≤20→∀ j,Canonical (states n j) := by
 intro n
 induction n with
 | zero => intro _ j;rw [initial];intro i;change 0<2147483647;omega
 | succ n ih =>
   intro hn j
   rw [cuts n (by omega) j]
   split
   · exact reply_canonical _ _
   · exact ih (by omega) j

/-- Apply CLOSED parent source on identical observed arguments and derive,
rather than assume, all parent Result clauses of the roots invocation. -/
theorem parent_clauses (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20),StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (NJZ_TreeParent.reply (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩))) :
 ∀ n (hn : n<20),StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (parent (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩)) := by
 intro n hn
 let current:=states n ⟨n,by omega⟩
 have domain : Canonical current:=domains states initial cuts n (by omega) _
 have child:=NJZ_TreeParent.source current current current current
  (NJZ_TreeParent.reply current current) 1 domain domain
  {left:=rfl,right:=rfl,output:=rfl,count:=rfl}
 rw [←child.1]
 exact cuts n hn

theorem roots (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20),StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (NJZ_TreeParent.reply (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩))) :
 ∀ j,states 20 j=root j.val :=
 NJZ_EmptyTree.roots states initial (parent_clauses states initial cuts)

theorem empty (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20),StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (NJZ_TreeParent.reply (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩)))
 (out : Tree) (constructor : EmptyCut (states 20) out) : out=NJZ_EmptyTree.empty :=
 NJZ_EmptyTree.empty_source _ (roots states initial cuts) out constructor

theorem default (states : Nat → Table) (initial : ∀ j,states 0 j=zero)
 (cuts : ∀ n (hn : n<20),StepCut (states n) (states (n+1)) ⟨n,hn⟩
   (NJZ_TreeParent.reply (states n ⟨n,by omega⟩) (states n ⟨n,by omega⟩)))
 (child out : Tree) (constructor : EmptyCut (states 20) child)
 (returnCut : DefaultCut child out) : out=NJZ_EmptyTree.default := by
 exact returnCut.trans (empty states initial cuts child constructor)

#print axioms reply_canonical
#print axioms domains
#print parent_clauses
#print axioms parent_clauses
#print roots
#print axioms roots
#print empty
#print axioms empty
#print default
#print axioms default
end NJZ_PoolRoot
