import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.NJL_TagChunk04
open Aeneas Aeneas.Std
def blocks : List Nat := [2,3,26,28,29,31,32,63,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,4,5,6,7,8]
def tags : List U32 := [1124073472#u32,1124073473#u32,1124073474#u32,1124073475#u32,1124073476#u32,1124073477#u32,1124073478#u32,1124073483#u32,1124073495#u32,1124073497#u32,1124073499#u32,1124073501#u32,1124073503#u32,1124073505#u32,1124073507#u32,1124073509#u32,1124073511#u32,1124073513#u32,1124073515#u32,1124073517#u32,1124073519#u32,1124073521#u32,1124073523#u32,1124073525#u32,1124073527#u32,1124073529#u32,1124073531#u32,1124073533#u32,1124073535#u32,1124073538#u32,1124073541#u32,1124073544#u32,1124073547#u32,1124073550#u32]
theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
end AspisR1.NJL_TagChunk04
