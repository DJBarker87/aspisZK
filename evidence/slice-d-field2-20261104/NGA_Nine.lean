import NGA_Step
set_option autoImplicit false
namespace NGA_Nine
open Aeneas Aeneas.Std Result NGA_Cell

def run : List Cell → Sums → Cache → Cache → Result Sums
 | [],s,_,_ => ok s
 | c::cs,s,l,r => do
   let next ← step s l r (uFin c.1) (uFin c.2)
   run cs next l r

def product (l r : Cache) (c : Cell) : Nat := (get l c).val*(get r c).val

/-- Each selected cell is untouched before its unique turn. The invariant is
restricted to remaining cells, so a fourth product is admitted without falsely
requiring a completed cell to satisfy the old pre-cell budget. -/
theorem loop (cells : List Cell) (nodup : cells.Nodup) (s : Sums) (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r)
 (hs : ∀ c ∈ cells, (get s c).val≤3*(2147483647-1)^2) :
 ∃ out, run cells s l r=ok out ∧
   ∀ d, (get out d).val=(get s d).val + if d∈cells then product l r d else 0 := by
 induction cells generalizing s with
 | nil => exact ⟨s,rfl,by intro d;simp⟩
 | cons c cs ih =>
   obtain ⟨notmem,tail⟩ := List.nodup_cons.mp nodup
   obtain ⟨next,hnext,vnext⟩ := NGA_Step.source s l r c
     (NGA_Step.bounded_get l hl c) (NGA_Step.bounded_get r hr c) (hs c (by simp))
   have nextbound : ∀ d∈cs, (get next d).val≤3*(2147483647-1)^2 := by
     intro d hd
     have hdc : d≠c := by intro h;subst d;exact notmem hd
     rw [vnext d,if_neg hdc,Nat.add_zero]
     exact hs d (by simp [hd])
   obtain ⟨out,hout,vout⟩ := ih tail next nextbound
   refine ⟨out,?_,?_⟩
   · simp only [run,hnext,bind_tc_ok];exact hout
   · intro d
     rw [vout d,vnext d]
     by_cases hdc : d=c
     · subst d;simp [notmem,product]
     · simp [List.mem_cons,hdc,product]

abbrev trace := NFT_ChannelModel.trace

theorem trace_nodup : trace.Nodup := by decide

theorem trace_complete (c : Cell) : c∈trace := by
 rcases c with ⟨i,j⟩
 fin_cases i <;> fin_cases j <;> simp [trace,NFT_ChannelModel.trace]

theorem source (s : Sums) (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r)
 (hs : ∀ c, (get s c).val≤3*(2147483647-1)^2) :
 ∃ out, run trace s l r=ok out ∧
   ∀ d, (get out d).val=(get s d).val+product l r d := by
 obtain ⟨out,ho,hv⟩ := loop trace trace_nodup s l r hl hr (by intro c _;exact hs c)
 exact ⟨out,ho,by intro d;simpa only [if_pos (trace_complete d)] using hv d⟩

#print axioms loop
#print axioms trace_nodup
#print axioms trace_complete
#print axioms source
end NGA_Nine
