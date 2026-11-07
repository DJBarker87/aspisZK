import NMX_R2_LengthGuard
set_option autoImplicit false
namespace NMX_R2_SevenList
/-- Only the seven-account branch produces these witnesses. -/
theorem shape {A : Type} (xs : List A) (count : xs.length = 7) :
 ∃ p m c l r e v, xs = [p,m,c,l,r,e,v] := by
 cases xs with
 | nil => simp only [List.length_cons,List.length_nil] at count; omega
 | cons p rest0 =>
   cases rest0 with
   | nil => simp only [List.length_cons,List.length_nil] at count; omega
   | cons m rest1 =>
     cases rest1 with
     | nil => simp only [List.length_cons,List.length_nil] at count; omega
     | cons c rest2 =>
       cases rest2 with
       | nil => simp only [List.length_cons,List.length_nil] at count; omega
       | cons l rest3 =>
         cases rest3 with
         | nil => simp only [List.length_cons,List.length_nil] at count; omega
         | cons r rest4 =>
           cases rest4 with
           | nil => simp only [List.length_cons,List.length_nil] at count; omega
           | cons e rest5 =>
             cases rest5 with
             | nil => simp only [List.length_cons,List.length_nil] at count; omega
             | cons v rest6 =>
               cases rest6 with
               | nil => exact ⟨p,m,c,l,r,e,v,rfl⟩
               | cons extra remaining => simp only [List.length_cons,List.length_nil] at count; omega
#print axioms shape
end NMX_R2_SevenList
