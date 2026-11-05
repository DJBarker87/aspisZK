import NHM_WindowBridge
import NHM_ArrayPreserve
set_option autoImplicit false
namespace NHM_EEncoding
open Aeneas Aeneas.Std Result AspisR1
abbrev NE := FIo_Install.NE
abbrev Words := Array U32 8#usize

def record (a : Words) : NE := NEI_WideConstruction.value
 (NHI_ScalarDomain.pick a 0 (by decide)) (NHI_ScalarDomain.pick a 1 (by decide))
 (NHI_ScalarDomain.pick a 2 (by decide)) (NHI_ScalarDomain.pick a 3 (by decide))
 (NHI_ScalarDomain.pick a 4 (by decide)) (NHI_ScalarDomain.pick a 5 (by decide))
 (NHI_ScalarDomain.pick a 6 (by decide)) (NHI_ScalarDomain.pick a 7 (by decide))

theorem roundtrip (x : NE) : record (NGM_RawWords.nativeWords x)=x := by
 cases x with | mk a b=>cases a with | mk c d=>cases b with | mk e f=>cases c;cases d;cases e;cases f;rfl

def encode {n : Usize} (a : Array NE n) : Array Words n :=
 ⟨a.val.map NGM_RawWords.nativeWords,by simpa only [List.length_map] using a.property⟩

def decode {n : Usize} (a : Array Words n) : Array NE n :=
 ⟨a.val.map record,by simpa only [List.length_map] using a.property⟩

theorem array_roundtrip {n : Usize} (a : Array NE n) : decode (encode a)=a := by
 apply Subtype.ext
 simp only [decode,encode,List.map_map]
 have same : (record ∘ NGM_RawWords.nativeWords)=id := funext roundtrip
 rw [same,List.map_id]

theorem injective {n : Usize} : Function.Injective (@encode n) := by
 intro a b h
 have mapped:=congrArg decode h
 simpa only [array_roundtrip] using mapped

theorem put {n : Usize} (a : Array NE n) (i : Usize) (x : NE) :
 encode (NHI_ArrayCells.put a i x)=NHI_ArrayCells.put (encode a) i (NGM_RawWords.nativeWords x) := by
 apply Subtype.ext
 exact List.map_set

#print axioms roundtrip
#print axioms array_roundtrip
#print axioms injective
#print axioms put
end NHM_EEncoding
