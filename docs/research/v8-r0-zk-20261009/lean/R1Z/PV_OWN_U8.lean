import R1Z.PV_OWN_View
set_option autoImplicit false
namespace R1Z.PV_OWN_U8
open PV_OWN_Bytes PV_OWN_View
/-- Exact one-byte representation, with no padding. -/
def encode (v : UInt8) : Bytes := fun i => if i=0 then some v else none

def codec : Codec UInt8 where
 width := 1
 alignment := 1
 positive_alignment := by decide
 encode := encode
 injective := by
  intro a b h
  have hh:=h 0 (by decide)
  simpa [encode] using hh

theorem initialized_byte (c : PV_OWN_Heap.Cell) (s : Nat) (v : UInt8)
 (h:Represents codec c s v) : c.contents s=some v := by
 simpa [codec,encode] using h.2 0 (by decide)
#print axioms initialized_byte
end R1Z.PV_OWN_U8
