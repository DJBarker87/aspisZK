import MultiproofConeP6Verify
import NJP_CopyFrame

set_option autoImplicit false
noncomputable section
namespace NJP_RowModel
open Aeneas Aeneas.Std Result
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev Digest := Fin 32 → U8
abbrev Request := Digest × Digest
structure Scratch where
 indices : Fin 16 → Nat
 values : Fin 16 → Digest
 n : Nat
 cursor : Nat

def index (s : Scratch) (i : Nat) : Nat := if h : i<16 then s.indices ⟨i,h⟩ else 0
def value (s : Scratch) (i : Nat) : Digest := if h : i<16 then s.values ⟨i,h⟩ else fun _ => 0#u8

def paired (s : Scratch) (i : Nat) : Prop :=
 i+1<s.n ∧ index s (i+1)=Nat.xor (index s i) 1
instance (s : Scratch) (i : Nat) : Decidable (paired s i) := inferInstanceAs (Decidable (_ ∧ _))

def window (nodes : Nat → U8) (cursor : Nat) : Digest := fun j => nodes (cursor+j.val)
def occupiedRequest (s : Scratch) (i : Nat) : Request := (value s i,value s (i+1))
def siblingRequest (s : Scratch) (i : Nat) (nodes : Nat → U8) : Request :=
 if index s i%2=0 then (value s i,window nodes s.cursor) else (window nodes s.cursor,value s i)

def write (s : Scratch) (i w cursor : Nat) (reply : Digest) : Scratch :=
 {s with indices:=fun k => if k.val=w then index s i/2 else s.indices k,
   values:=fun k => if k.val=w then reply else s.values k,cursor:=cursor}

inductive Row where
 | stop (state : Scratch)
 | next (state : Scratch) (i w : Nat)

abbrev Run := Program Request Digest (Result Row)

/-- Source-ordered one-iteration G, in natural scalar and full byte carriers.
Its relation to the emitted/cohort carriers is a separate obligation. -/
def node (nodes : Nat → U8) (length : Nat) (s : Scratch) (i w : Nat) : Run :=
 if i<s.n then
   if paired s i then
     .ask (occupiedRequest s i) fun reply => .done (ok (.next (write s i w s.cursor reply) (i+2) (w+1)))
   else if s.cursor+32≤length then
     .ask (siblingRequest s i nodes) fun reply =>
       .done (ok (.next (write s i w (s.cursor+32) reply) (i+1) (w+1)))
   else .done (ok (.stop s))
 else .done (ok (.next s i w))

/-- The own input invariant establishes every scalar/slice/write bound used
by the split cuts, independent of sorting or digest values. -/
def Domain (length : Nat) (s : Scratch) (i w : Nat) : Prop :=
 0<s.n ∧ s.n≤16 ∧ i≤s.n ∧ w≤i ∧ s.cursor≤length ∧ length≤9216

theorem active_bounds (length : Nat) (s : Scratch) (i w : Nat)
    (domain : Domain length s i w) (active : i<s.n) : i<16 ∧ w<16 ∧ s.cursor+32<2^64 := by
 obtain ⟨positive,size,_,write,at,bound⟩ := domain
 omega

theorem paired_bound (s : Scratch) (i : Nat) (size : s.n≤16) (both : paired s i) :
 i+1<16 ∧ i+2≤s.n := by
 obtain ⟨next,_⟩ := both
 omega

theorem write_frame (s : Scratch) (i w cursor : Nat) (reply : Digest) (k : Fin 16)
    (different : k.val≠w) :
 (write s i w cursor reply).indices k=s.indices k ∧
 (write s i w cursor reply).values k=s.values k := by
 simp only [write,if_neg different,and_self]

theorem write_selected (s : Scratch) (i : Nat) (w : Fin 16) (cursor : Nat) (reply : Digest) :
 (write s i w.val cursor reply).indices w=index s i/2 ∧
 (write s i w.val cursor reply).values w=reply := by
 simp only [write,ite_true,and_self]

theorem occupied_observation (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (active : i<s.n) (both : paired s i) :
 eval H (node nodes length s i w)=
 ([(occupiedRequest s i,H (occupiedRequest s i))],
   ok (.next (write s i w s.cursor (H (occupiedRequest s i))) (i+2) (w+1))) := by
 simp only [node,if_pos active,if_pos both,eval]

theorem sibling_observation (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (active : i<s.n) (single : ¬paired s i)
    (available : s.cursor+32≤length) :
 eval H (node nodes length s i w)=
 ([(siblingRequest s i nodes,H (siblingRequest s i nodes))],
   ok (.next (write s i w (s.cursor+32) (H (siblingRequest s i nodes))) (i+1) (w+1))) := by
 simp only [node,if_pos active,if_neg single,if_pos available,eval]

theorem missing_observation (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (active : i<s.n) (single : ¬paired s i)
    (missing : length<s.cursor+32) : eval H (node nodes length s i w)=([],ok (.stop s)) := by
 simp only [node,if_pos active,if_neg single,if_neg (show ¬s.cursor+32≤length by omega),eval]

theorem exhausted_observation (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (exhausted : s.n≤i) :
 eval H (node nodes length s i w)=([],ok (.next s i w)) := by
 simp only [node,if_neg (show ¬i<s.n by omega),eval]

#print active_bounds
#print axioms active_bounds
#print paired_bound
#print axioms paired_bound
#print write_frame
#print axioms write_frame
#print write_selected
#print axioms write_selected
#print occupied_observation
#print axioms occupied_observation
#print sibling_observation
#print axioms sibling_observation
#print missing_observation
#print axioms missing_observation
#print exhausted_observation
#print axioms exhausted_observation
end NJP_RowModel
end
