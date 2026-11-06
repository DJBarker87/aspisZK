import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.NJL_TagChunk06
open Aeneas Aeneas.Std
def blocks : List Nat := [63,63,57,58,59,60,61,62,63,1,25,26,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,4]
def tags : List U32 := [1124073488#u32,1124073490#u32,1124073542#u32,1124073554#u32,1124073566#u32,1124073578#u32,1124073590#u32,1124073602#u32,1124073492#u32,1124073479#u32,1124073480#u32,1124073481#u32,1124073493#u32,1124073496#u32,1124073498#u32,1124073500#u32,1124073502#u32,1124073504#u32,1124073506#u32,1124073508#u32,1124073510#u32,1124073512#u32,1124073514#u32,1124073516#u32,1124073518#u32,1124073520#u32,1124073522#u32,1124073524#u32,1124073526#u32,1124073528#u32,1124073530#u32,1124073532#u32,1124073534#u32,1124073537#u32]
theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
end AspisR1.NJL_TagChunk06
