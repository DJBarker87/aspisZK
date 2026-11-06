import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.NJL_TagChunk00
open Aeneas Aeneas.Std
def blocks : List Nat := [63,4,57,63,57,58,59,60,61,62,63,63,57,58,59,60,61,62,63,57,58,59,60,61,62,1,2,25,27,28,30,31,0,32]
def tags : List U32 := [1124073486#u32,1124073490#u32,1124073491#u32,1124073487#u32,1124073537#u32,1124073549#u32,1124073561#u32,1124073573#u32,1124073585#u32,1124073597#u32,1124073488#u32,1124073489#u32,1124073540#u32,1124073552#u32,1124073564#u32,1124073576#u32,1124073588#u32,1124073600#u32,1124073495#u32,1124073543#u32,1124073555#u32,1124073567#u32,1124073579#u32,1124073591#u32,1124073603#u32,1124073472#u32,1124073473#u32,1124073474#u32,1124073475#u32,1124073476#u32,1124073477#u32,1124073478#u32,1124073479#u32,1124073492#u32]
theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
end AspisR1.NJL_TagChunk00
