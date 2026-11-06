import NKJ_NativeStep
import NKJ_Accumulate
set_option autoImplicit false
namespace NKJ_NativeFold
open Aeneas Aeneas.Std Result NGA_Cell

def run : List Cell → Sums → Cache → Cache → Result Sums
 | [],s,_,_ => ok s
 | c::cs,s,l,r => do
   let next ← NKJ_NativeStep.run s l r c
   run cs next l r

theorem source (cells : List Cell) (nodup : cells.Nodup) (s : Sums) (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r)
 (hs : ∀ c∈cells, (get s c).val≤3*(2147483647-1)^2) :
 run cells s l r=NGA_Nine.run cells s l r := by
 induction cells generalizing s with
 | nil => rfl
 | cons c cs ih =>
   obtain ⟨notmem,tail⟩ := List.nodup_cons.mp nodup
   have hcell := hs c (by simp)
   have assoc := NKJ_NativeStep.source s l r c
    (NGA_Step.bounded_get l hl c) (NGA_Step.bounded_get r hr c) hcell
   obtain ⟨next,hnext,vnext⟩ := NGA_Step.source s l r c
    (NGA_Step.bounded_get l hl c) (NGA_Step.bounded_get r hr c) hcell
   have nextbound : ∀ d∈cs, (get next d).val≤3*(2147483647-1)^2 := by
    intro d hd
    have hdc : d≠c := by intro h;subst d;exact notmem hd
    rw [vnext d,if_neg hdc,Nat.add_zero]
    exact hs d (by simp [hd])
   simp only [run,NGA_Nine.run,assoc,hnext,bind_tc_ok]
   exact ih tail next nextbound

/-- The two frozen Range(0,3) loops visit every cell once, in source order. -/
theorem order :
 (List.finRange 3).flatMap (fun i => (List.finRange 3).map (fun j => (i,j)))=NGA_Nine.trace := by rfl

def accumulate (s : Sums) (left right : NGA_Cache.Q) : Result Sums := do
 let l ← NGA_Cache.prelude left
 let r ← NGA_Cache.prelude right
 run NGA_Nine.trace s l r

theorem accumulate_ref (s : Sums) (left right : NGA_Cache.Q)
 (hl : NGA_Cache.Canonical left) (hr : NGA_Cache.Canonical right)
 (hs : ∀ c, (get s c).val≤3*(2147483647-1)^2) :
 accumulate s left right=NKJ_Extracted.field.NKJ_reference.NKJ_accumulate s (NKJ_Cache.words left) (NKJ_Cache.words right) := by
 rw [NKJ_Accumulate.source s left right hl hr hs]
 obtain ⟨l,hlrun,hlc,_⟩ := NGA_CacheDomain.source left hl
 obtain ⟨r,hrrun,hrc,_⟩ := NGA_CacheDomain.source right hr
 simp only [accumulate,NGA_Accumulate.sourceModel,hlrun,hrrun,bind_tc_ok]
 exact source NGA_Nine.trace NGA_Nine.trace_nodup s l r hlc hrc (fun c _ => hs c)
#print axioms source
#print axioms order
#print axioms accumulate_ref
end NKJ_NativeFold
