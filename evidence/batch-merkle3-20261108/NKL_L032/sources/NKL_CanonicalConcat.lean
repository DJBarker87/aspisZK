import MultiproofConeCanonical
set_option autoImplicit false
noncomputable section
namespace NKL_CanonicalConcat
open AspisR1 OraclePortCompactDraft MultiproofConeCanonical
open AspisV8R19.DuplexFrames

theorem append (left right : Bytes) (aligned:left.length%4=0) :
 canonical (left++right) ↔ canonical left ∧ canonical right := by
 generalize length:left.length=n
 induction n using Nat.strong_induction_on generalizing left with
 | h n ih =>
   cases left with
   | nil => simp [canonical]
   | cons a left =>
     cases left with
     | nil => simp at aligned
     | cons b left =>
       cases left with
       | nil => simp at aligned
       | cons c left =>
         cases left with
         | nil => simp at aligned
         | cons d rest =>
           have tail : rest.length%4=0 := by simp only [List.length_cons] at aligned;omega
           have step:=ih rest.length (by simp only [List.length_cons] at length;omega) rest tail rfl
           simp only [List.cons_append,canonical_four]
           rw [step]
           exact and_assoc.symm

theorem partition (bs : Bytes) (n : Nat) (fits:n≤bs.length) (aligned:n%4=0) :
 canonical bs ↔ canonical (bs.take n) ∧ canonical (bs.drop n) := by
 have left:(bs.take n).length%4=0 := by rw [List.length_take,Nat.min_eq_left fits];exact aligned
 simpa only [List.take_append_drop] using append (bs.take n) (bs.drop n) left

#print axioms append
#print axioms partition
end NKL_CanonicalConcat
end
