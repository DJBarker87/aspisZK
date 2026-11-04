import NGA_Cell
import NGA_CacheDomain
set_option autoImplicit false
namespace NGA_Step
open Aeneas Aeneas.Std Result WP
open NGA_Cell

theorem bounded_get (a : Cache) (h : NGA_CacheDomain.Bounded a) (c : Cell) :
 (get a c).val<2147483647 := by
 exact h (at3 a c.1) (List.getElem_mem _) (get a c) (List.getElem_mem _)

theorem source (s : Sums) (left right : Cache) (c : Cell)
 (hl : (get left c).val<2147483647) (hr : (get right c).val<2147483647)
 (hs : (get s c).val≤3*(2147483647-1)^2) :
 ∃ out : Sums,
   step s left right (uFin c.1) (uFin c.2)=ok out ∧
   ∀ d : Cell, (get out d).val=(get s d).val + if d=c then (get left c).val*(get right c).val else 0 := by
 obtain ⟨v,hv,hval⟩ := NFT_ChannelFour.generated_step (get left c) (get right c) (get s c) hl hr hs
 obtain ⟨row,back,hm,hrow,hback⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_mut_ok s (uFin c.1) (by
   rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val];exact c.1.isLt)
 have hrow' : row=at3 s c.1 := by simpa only [at3,AspisR1PoseidonPreparedIndexProductBounds.uFin_val] using hrow
 subst row
 have hu : Array.update (at3 s c.1) (uFin c.2) v=ok ((at3 s c.1).set (uFin c.2) v) := by
   obtain ⟨out,hout,hval⟩ := WP.spec_imp_exists (Array.update_spec (at3 s c.1) (uFin c.2) v (by
     simpa [Array.length,AspisR1PoseidonPreparedIndexProductBounds.uFin_val,(at3 s c.1).property] using c.2.isLt))
   simpa only [hval] using hout
 refine ⟨set s c v,?_,?_⟩
 · simp only [step,index,bind_tc_ok]
   change (do
     let p ← UScalar.mul (UScalar.cast .U64 (get left c)) (UScalar.cast .U64 (get right c))
     let upd ← UScalar.add (get s c) p
     let (r,b) ← Array.index_mut_usize s (uFin c.1)
     let r ← Array.update r (uFin c.2) upd
     ok (b r))=ok (set s c v)
   rw [inlineScalar_bind,hv]
   simp only [bind_tc_ok,hm,hu,hback,set]
 · intro d
   rw [get_set]
   by_cases hd : d=c
   · subst d;simp only [if_pos rfl];exact hval
   · simp only [if_neg hd,Nat.add_zero]

#print axioms bounded_get
#print axioms source
end NGA_Step
