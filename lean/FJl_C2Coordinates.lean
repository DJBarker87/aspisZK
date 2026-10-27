import FJl_FixedIndex
import R1MixedLeafDecoder
set_option autoImplicit false
namespace AspisR1.FJl_C2Coordinates
open ExactLeafFieldCodec MixedLeafEncoding MixedLeafDecoder
/-- The SAME C2 quartet contains two QM31 coordinates per slot. -/
theorem slot (bytes : List Byte) (c : C2) (run : decodeC2 bytes=some c) (s : Fin 4) :
    decodeC2Slot ((bytes.drop (32*s.val)).take 32)=some (c s) :=
  FJl_FixedIndex.read _ _ _ bytes c run s

theorem coordinate (bytes : List Byte) (c : C2) (run : decodeC2 bytes=some c)
    (s : Fin 4) (l : Fin 2) :
    decodeQM31 ((((bytes.drop (32*s.val)).take 32).drop (16*l.val)).take 16)=some (c s l) :=
  FJl_FixedIndex.read _ _ _ _ (c s) (slot bytes c run s) l
#print axioms slot
#print axioms coordinate
end AspisR1.FJl_C2Coordinates
