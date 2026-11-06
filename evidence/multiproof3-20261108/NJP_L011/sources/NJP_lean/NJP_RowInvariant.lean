import NJP_RowModel

set_option autoImplicit false
noncomputable section
namespace NJP_RowInvariant
open Aeneas Aeneas.Std Result NJP_RowModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def Progress (length : Nat) (s : Scratch) (i w : Nat) : Row → Prop
 | .stop stopped => stopped=s
 | .next after ni nw =>
   after.n=s.n  ∧  Domain length after ni nw  ∧  i<ni  ∧  nw=w+1

theorem occupied_domain (length : Nat) (s : Scratch) (i w : Nat) (reply : Digest)
    (domain : Domain length s i w) (both : paired s i) :
    Domain length (write s i w s.cursor reply) (i+2) (w+1) := by
 obtain ⟨positive,size,read,writeBound,cursorBound,byteBound⟩ := domain
 obtain ⟨readNext,_⟩ := both
 simp only [Domain,write]
 exact ⟨positive,size,by omega,by omega,cursorBound,byteBound⟩

theorem sibling_domain (length : Nat) (s : Scratch) (i w : Nat) (reply : Digest)
    (domain : Domain length s i w) (active : i<s.n) (available : s.cursor+32 ≤ length) :
    Domain length (write s i w (s.cursor+32) reply) (i+1) (w+1) := by
 obtain ⟨positive,size,read,writeBound,cursorBound,byteBound⟩ := domain
 simp only [Domain,write]
 exact ⟨positive,size,by omega,by omega,available,byteBound⟩

theorem node_progress (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (domain : Domain length s i w) (active : i<s.n) :
    ∃ out, (eval H (node nodes length s i w)).2=ok out  ∧  Progress length s i w out := by
 by_cases both : paired s i
 · rw [occupied_observation H nodes length s i w active both]
   refine ⟨_,rfl,rfl,occupied_domain length s i w _ domain both,by omega,rfl⟩
 · by_cases available : s.cursor+32 ≤ length
   · rw [sibling_observation H nodes length s i w active both available]
     refine ⟨_,rfl,rfl,sibling_domain length s i w _ domain active available,by omega,rfl⟩
   · rw [missing_observation H nodes length s i w active both (by omega)]
     exact ⟨_,rfl,rfl⟩

#print occupied_domain
#print axioms occupied_domain
#print sibling_domain
#print axioms sibling_domain
#print node_progress
#print axioms node_progress
end NJP_RowInvariant
end
