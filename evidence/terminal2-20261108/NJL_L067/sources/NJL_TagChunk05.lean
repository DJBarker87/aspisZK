import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.NJL_TagChunk05
open Aeneas Aeneas.Std
def blocks : List Nat := [9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,54,55,56,57,58,59,60,61,62,63,63,57,58,59,60,61,62,63]
def tags : List U32 := [1124073553#u32,1124073556#u32,1124073559#u32,1124073562#u32,1124073565#u32,1124073568#u32,1124073571#u32,1124073574#u32,1124073577#u32,1124073580#u32,1124073583#u32,1124073586#u32,1124073589#u32,1124073592#u32,1124073595#u32,1124073598#u32,1124073601#u32,1124073604#u32,1124073607#u32,1124073536#u32,1124073548#u32,1124073560#u32,1124073572#u32,1124073584#u32,1124073596#u32,1124073484#u32,1124073485#u32,1124073539#u32,1124073551#u32,1124073563#u32,1124073575#u32,1124073587#u32,1124073599#u32,1124073486#u32]
theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
end AspisR1.NJL_TagChunk05
