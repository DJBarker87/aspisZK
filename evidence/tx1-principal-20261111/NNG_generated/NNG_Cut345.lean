import NNG_ReifyAccounts345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Cut345
open Aeneas Aeneas.Std RSL

/-- Oversized logical data has no native slice. Keep its zero-test verdict;
all nonzero representatives have one byte. No large buffer is constructed. -/
def cut (b : Bytes) : Bytes :=
 if b.length≤Usize.max then b else if b.all (· == 0) then [] else [1]

theorem bound (b : Bytes) : (cut b).length≤Usize.max := by
 unfold cut
 split
 · assumption
 · cases hz : b.all (· == 0) <;>
    simp only [hz,Bool.false_eq_true,if_false,if_true,List.length_nil,List.length_cons] <;> scalar_tac
#print axioms bound

theorem fixed (b : Bytes) (h : b.length≤Usize.max) : cut b=b := by
 unfold cut
 rw [if_pos h]
#print axioms fixed

theorem zero (b : Bytes) : requireZero (cut b)=requireZero b := by
 unfold cut
 split
 · rfl
 · cases hz : b.all (· == 0) <;> simp only [hz,Bool.false_eq_true,if_false,if_true,requireZero] <;> rfl
#print axioms zero

theorem width (b : Bytes) (n : Nat) (positive : 1<n) (fits : n≤Usize.max) :
 ((cut b).length != n)=(b.length != n) := by
 unfold cut
 split
 · rfl
 · rename_i large
   have wrong : b.length≠n := by omega
   cases b.all (· == 0) <;> simp only [Bool.false_eq_true,if_false,if_true,List.length_nil,List.length_cons]
   · have small : 1≠n := by omega
     apply Bool.eq_iff_iff.mpr
     simp only [bne_iff_ne]
     exact ⟨fun _=>wrong,fun _=>small⟩
   · have small : 0≠n := by omega
     apply Bool.eq_iff_iff.mpr
     simp only [bne_iff_ne]
     exact ⟨fun _=>wrong,fun _=>small⟩
#print axioms width

theorem decode (b : Bytes) : LIBC_S1.decode (cut b)=LIBC_S1.decode b := by
 by_cases fit : b.length≤Usize.max
 · rw [fixed b fit]
 · have full : 1880≤Usize.max := by scalar_tac
   have original : b.length≠1880 := by omega
   have projected : (cut b).length≠1880 := by
    have h := width b 1880 (by decide) full
    intro eq
    have hn : (b.length !=1880)=true := bne_iff_ne.mpr original
    rw [eq,bne_self_eq_false,hn] at h
    cases h
   unfold LIBC_S1.decode
   rw [dif_neg projected,dif_neg original]
#print axioms decode
end AspisR1.NNG_Cut345
