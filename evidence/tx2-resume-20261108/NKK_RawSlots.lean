import NKK_RawChain
import NJJ_ResumeDomains
set_option autoImplicit false
noncomputable section
namespace NKK_RawSlots
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_NativeRaw

/-- The two native eight-read query windows are used at their actual source
positions. This domain follows from the header and preceding child cursors. -/
theorem query8 (r : Reader) (block : Fin 2)
 (length : r.bytes.val.length=1768) (cursor : r.at.val=320+32*block.val) :
 ∃ (bs : List (Array U8 4#usize)) (last : Reader), NKK_NativeRaw.Chain 4#usize r bs last ∧ bs.length=8 ∧
 reads 4#usize 8 r=ok (bs,last) ∧ last.bytes=r.bytes ∧
 last.at.val=352+32*block.val := by
 obtain ⟨bs,last,chain,size,run⟩:=read_chain 4#usize 8 r (by change r.at.val+4*8≤r.bytes.val.length;rw [length,cursor];omega)
 refine ⟨bs,last,chain,size,run,backing chain,?_⟩
 have advance:=advance chain
 simp only [size] at advance
 change last.at.val=r.at.val+4*8 at advance
 omega

theorem query6 (r : Reader)
 (length : r.bytes.val.length=1768) (cursor : r.at.val=384) :
 ∃ (bs : List (Array U8 4#usize)) (last : Reader), NKK_NativeRaw.Chain 4#usize r bs last ∧ bs.length=6 ∧
 reads 4#usize 6 r=ok (bs,last) ∧ last.bytes=r.bytes ∧ last.at.val=408 := by
 obtain ⟨bs,last,chain,size,run⟩:=read_chain 4#usize 6 r (by change r.at.val+4*6≤r.bytes.val.length;rw [length,cursor];omega)
 refine ⟨bs,last,chain,size,run,backing chain,?_⟩
 have advance:=advance chain
 simp only [size] at advance
 change last.at.val=r.at.val+4*6 at advance
 omega

theorem roots (r : Reader)
 (length : r.bytes.val.length=1768) (cursor : r.at.val=80) :
 ∃ (bs : List (Array U8 32#usize)) (last : Reader), NKK_NativeRaw.Chain 32#usize r bs last ∧ bs.length=3 ∧
 reads 32#usize 3 r=ok (bs,last) ∧ last.bytes=r.bytes ∧ last.at.val=176 := by
 obtain ⟨bs,last,chain,size,run⟩:=read_chain 32#usize 3 r (by change r.at.val+32*3≤r.bytes.val.length;rw [length,cursor];omega)
 refine ⟨bs,last,chain,size,run,backing chain,?_⟩
 have advance:=advance chain
 simp only [size] at advance
 change last.at.val=r.at.val+32*3 at advance
 omega

#print axioms query8
#print axioms query6
#print axioms roots
end NKK_RawSlots
