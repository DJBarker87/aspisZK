import NHM_WindowExtracted
import NHM_DotPacket
import NHI_WordEncoding
set_option autoImplicit false
namespace NHM_WindowBridge
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := NHM_DotPacket.Dot
abbrev pick := @NHI_ScalarDomain.pick

def words (d : Dot) : Array U64 8#usize := Array.make 8#usize
 [pick d.c0.sums 0 (by decide),pick d.c0.sums 1 (by decide),
  pick d.c0.sums 2 (by decide),pick d.c0.sums 3 (by decide),
  pick d.c1.sums 0 (by decide),pick d.c1.sums 1 (by decide),
  pick d.c1.sums 2 (by decide),pick d.c1.sums 3 (by decide)]

def record (a : Array U64 8#usize) (count : Usize) : Dot :=
 ⟨⟨Array.make 4#usize [pick a 0 (by decide),pick a 1 (by decide),pick a 2 (by decide),pick a 3 (by decide)]⟩,
  ⟨Array.make 4#usize [pick a 4 (by decide),pick a 5 (by decide),pick a 6 (by decide),pick a 7 (by decide)]⟩,count⟩

theorem roundtrip (d : Dot) : record (words d) d.count=d := by
 rcases d with ⟨⟨left⟩,⟨right⟩,count⟩
 obtain ⟨a,b,c,d,hl⟩ := NGM_ArrayFour.shape left
 obtain ⟨e,f,g,h,hr⟩ := NGM_ArrayFour.shape right
 subst left
 subst right
 rfl

theorem injective (a b : Dot) (same : (words a,a.count)=(words b,b.count)) : a=b := by
 have mapped := congrArg (fun p=>record p.1 p.2) same
 simpa only [roundtrip] using mapped

def rejected : core.result.Result Unit Unit→Bool
 | .Ok _=>false
 | .Err _=>true

def reply : core.result.Result Unit Unit→core.result.Result Unit NHM_WindowRef.NHM_WindowError
 | .Ok _=>.Ok ()
 | .Err _=>.Err .Parse

/-- The compiled reference records the exact complete child reply and mutation;
instantiate it with the actual push packet, including its rejecting arm. -/
theorem source (x : NHM_DotPacket.NE) (q : NHM_DotPacket.NQ) (after : Dot)
 (r : core.result.Result Unit Unit) :
 NHM_WindowRef.window_ref (NGM_RawWords.nativeWords x) (NHI_WordEncoding.words q)
  (words after) after.count (rejected r)=
 ok (reply r,words after,after.count,NGM_RawWords.nativeWords x,NHI_WordEncoding.words q) := by
 cases r with
 | Ok u=>cases u;rfl
 | Err u=>cases u;rfl

#print axioms roundtrip
#print axioms injective
#print axioms source
end NHM_WindowBridge
