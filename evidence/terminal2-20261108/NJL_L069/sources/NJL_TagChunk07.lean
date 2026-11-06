import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.NJL_TagChunk07
open Aeneas Aeneas.Std
def blocks : List Nat := [5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,54,55,56,57,58,59,60,61,62,63,63,63,26,33]
def tags : List U32 := [1124073540#u32,1124073543#u32,1124073546#u32,1124073549#u32,1124073552#u32,1124073555#u32,1124073558#u32,1124073561#u32,1124073564#u32,1124073567#u32,1124073570#u32,1124073573#u32,1124073576#u32,1124073579#u32,1124073582#u32,1124073585#u32,1124073588#u32,1124073591#u32,1124073594#u32,1124073597#u32,1124073600#u32,1124073603#u32,1124073606#u32,1124073545#u32,1124073557#u32,1124073569#u32,1124073581#u32,1124073593#u32,1124073605#u32,1124073487#u32,1124073489#u32,1124073491#u32,1124073482#u32,1124073494#u32]
theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
end AspisR1.NJL_TagChunk07
