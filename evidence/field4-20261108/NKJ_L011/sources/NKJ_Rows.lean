import NKJ_Row
import NGA_ArrayExt
set_option autoImplicit false
namespace NKJ_Rows
open Aeneas Aeneas.Std Result NGA_Cell

def run (s : Sums) (l r : Cache) : Result Sums := do
 let a ← NKJ_Extracted.field.NKJ_reference.NKJ_row (at3 s 0) (at3 l 0) (at3 r 0)
 let b ← NKJ_Extracted.field.NKJ_reference.NKJ_row (at3 s 1) (at3 l 1) (at3 r 1)
 let c ← NKJ_Extracted.field.NKJ_reference.NKJ_row (at3 s 2) (at3 l 2) (at3 r 2)
 ok (Array.make 3#usize [a,b,c])

theorem value (s : Sums) (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r)
 (hs : ∀ d, (get s d).val≤3*(2147483647-1)^2) :
 ∃ out, run s l r=ok out ∧
 ∀ d, (get out d).val=(get s d).val+NGA_Nine.product l r d := by
 obtain ⟨a,ha,va⟩ := NKJ_Row.value (at3 s 0) (at3 l 0) (at3 r 0)
  (fun j => NGA_Step.bounded_get l hl (0,j)) (fun j => NGA_Step.bounded_get r hr (0,j)) (fun j => hs (0,j))
 obtain ⟨b,hb,vb⟩ := NKJ_Row.value (at3 s 1) (at3 l 1) (at3 r 1)
  (fun j => NGA_Step.bounded_get l hl (1,j)) (fun j => NGA_Step.bounded_get r hr (1,j)) (fun j => hs (1,j))
 obtain ⟨c,hc,vc⟩ := NKJ_Row.value (at3 s 2) (at3 l 2) (at3 r 2)
  (fun j => NGA_Step.bounded_get l hl (2,j)) (fun j => NGA_Step.bounded_get r hr (2,j)) (fun j => hs (2,j))
 refine ⟨Array.make 3#usize [a,b,c],?_,?_⟩
 · simp only [run,ha,hb,hc,bind_tc_ok]
 · rintro ⟨i,j⟩
   fin_cases i
   · simpa [get,at3,Array.make,NGA_Nine.product] using va j
   · simpa [get,at3,Array.make,NGA_Nine.product] using vb j
   · simpa [get,at3,Array.make,NGA_Nine.product] using vc j

theorem source (s : Sums) (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r)
 (hs : ∀ d, (get s d).val≤3*(2147483647-1)^2) :
 run s l r=NGA_Nine.run NGA_Nine.trace s l r := by
 obtain ⟨out,ho,vo⟩ := value s l r hl hr hs
 obtain ⟨out',ho',vo'⟩ := NGA_Nine.source s l r hl hr hs
 have same : out=out' := NGA_ArrayExt.source out out' (fun d => (vo d).trans (vo' d).symm)
 rw [ho,ho',same]
#print axioms value
#print axioms source
end NKJ_Rows
