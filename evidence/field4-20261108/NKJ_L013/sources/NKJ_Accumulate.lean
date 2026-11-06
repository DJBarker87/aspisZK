import NKJ_Cache
import NKJ_Rows
set_option autoImplicit false
namespace NKJ_Accumulate
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Q := NGA_Cache.Q

theorem unroll (s : Sums) (left right : Q) :
 NKJ_Extracted.field.NKJ_reference.NKJ_accumulate s (NKJ_Cache.words left) (NKJ_Cache.words right) = (do
 let l ← NKJ_Extracted.field.NKJ_reference.NKJ_channels (NKJ_Cache.words left)
 let r ← NKJ_Extracted.field.NKJ_reference.NKJ_channels (NKJ_Cache.words right)
 NKJ_Rows.run s l r) := by
 simp only [NKJ_Extracted.field.NKJ_reference.NKJ_accumulate,NKJ_Rows.run]
 congr 1;funext l;congr 1;funext r
 simp only [NKJ_Row.index0,NKJ_Row.index1,NKJ_Row.index2,bind_tc_ok]

theorem source (s : Sums) (left right : Q)
 (hl : NGA_Cache.Canonical left) (hr : NGA_Cache.Canonical right)
 (hs : ∀ d, (get s d).val≤3*(2147483647-1)^2) :
 NKJ_Extracted.field.NKJ_reference.NKJ_accumulate s (NKJ_Cache.words left) (NKJ_Cache.words right)=
 NGA_Accumulate.sourceModel s left right := by
 obtain ⟨l,hlrun,hlc,_⟩ := NGA_CacheDomain.source left hl
 obtain ⟨r,hrrun,hrc,_⟩ := NGA_CacheDomain.source right hr
 rw [unroll,NKJ_Cache.source left hl,NKJ_Cache.source right hr]
 simp only [NGA_Accumulate.sourceModel,hlrun,hrrun,bind_tc_ok]
 exact NKJ_Rows.source s l r hlc hrc hs

#print axioms unroll
#print axioms source
end NKJ_Accumulate
