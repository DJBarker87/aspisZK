import NCJ_FieldTotal
import MultiproofConeEndian
import MultiproofConeCanonicalAppend
import NIF_ScanDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_ByteDomain
open Aeneas Aeneas.Std Result OraclePortCompactDraft MultiproofConeCanonical
/-- Every selected four-byte word of a canonical fixed32 carrier is accepted
by the emitted M31 decoder, using its retained all-input codec bridge. -/
theorem fixed32 (part : Array U8 32#usize)
 (canonical : OraclePortCompactDraft.canonical (bytesOf part.val)) :
 NCJ_FieldTotal.Canonical part := by
 intro i
 let a : Array U8 4#usize := Array.make 4#usize
   [part.val[4*i.val]!,part.val[4*i.val+1]!,part.val[4*i.val+2]!,part.val[4*i.val+3]!]
 have same : List.ofFn (M31ParserArray.arrayBytes a)=slice (bytesOf part.val) (4*i.val) 4 := by
   apply List.ext_getElem
   · simp [slice,bytesOf,part.property];omega
   · intro j hj hj2
     have small : j<4 := by simpa using hj
     interval_cases j <;> simp [M31ParserArray.arrayBytes,a,Array.make,bytesOf,slice,
       List.getElem!_eq_getElem,show 4*i.val<part.val.length by rw [part.property];omega,
       show 4*i.val+1<part.val.length by rw [part.property];omega,
       show 4*i.val+2<part.val.length by rw [part.property];omega,
       show 4*i.val+3<part.val.length by rw [part.property];omega]
 have h:=canonical.2 i.val (by simp [bytesOf,part.property];omega)
 rw [←same,MultiproofConeEndian.little_four] at h
 exact (MultiproofConeEndian.strict_word_iff a).mpr h
#print axioms fixed32
end AspisR1.NIF_ByteDomain
