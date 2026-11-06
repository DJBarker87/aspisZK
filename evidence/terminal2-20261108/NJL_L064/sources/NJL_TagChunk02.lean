import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.NJL_TagChunk02
open Aeneas Aeneas.Std
def blocks : List Nat := [16,17,18,19,20,21,22,23,24,54,55,0,2,3,28,31,57,58,59,60,61,62,57,58,59,60,61,62,57,58,59,60,61,62]
def tags : List U32 := [1124073575#u32,1124073578#u32,1124073581#u32,1124073584#u32,1124073587#u32,1124073590#u32,1124073593#u32,1124073596#u32,1124073599#u32,1124073602#u32,1124073605#u32,1124073480#u32,1124073481#u32,1124073482#u32,1124073484#u32,1124073485#u32,1124073546#u32,1124073558#u32,1124073570#u32,1124073582#u32,1124073594#u32,1124073606#u32,1124073538#u32,1124073550#u32,1124073562#u32,1124073574#u32,1124073586#u32,1124073598#u32,1124073541#u32,1124073553#u32,1124073565#u32,1124073577#u32,1124073589#u32,1124073601#u32]
theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
end AspisR1.NJL_TagChunk02
