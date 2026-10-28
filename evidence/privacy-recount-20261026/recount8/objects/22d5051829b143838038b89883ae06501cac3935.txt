import R1Z.PV_CB_ArrayTransport
import R1Z.PV_CB_Op118Transport
/-! PREPARED: instantiate after fresh extraction and field-codec compilation. -/
set_option autoImplicit false
namespace R1Z.PV_CB_Op118Transport
open Aeneas Aeneas.Std PV_CB_ArrayTransport

def encodeArray (x : Array N 10#usize) : Array R 10#usize := mapArray encode x
def decodeArray (x : Array R 10#usize) : Array N 10#usize := mapArray decode x
def encodePoints (x : Array (Array N 10#usize) 3#usize) :
    Array (Array R 10#usize) 3#usize := mapArray encodeArray x
def decodePoints (x : Array (Array R 10#usize) 3#usize) :
    Array (Array N 10#usize) 3#usize := mapArray decodeArray x

theorem native_array_roundtrip (x : Array N 10#usize) :
    decodeArray (encodeArray x) = x := roundtrip encode decode native_roundtrip x
theorem extracted_array_roundtrip (x : Array R 10#usize) :
    encodeArray (decodeArray x) = x := roundtrip decode encode extracted_roundtrip x
theorem native_points_roundtrip (x : Array (Array N 10#usize) 3#usize) :
    decodePoints (encodePoints x) = x :=
  roundtrip encodeArray decodeArray native_array_roundtrip x
theorem extracted_points_roundtrip (x : Array (Array R 10#usize) 3#usize) :
    encodePoints (decodePoints x) = x :=
  roundtrip decodeArray encodeArray extracted_array_roundtrip x

#print axioms native_array_roundtrip
#print axioms extracted_array_roundtrip
#print axioms native_points_roundtrip
#print axioms extracted_points_roundtrip
end R1Z.PV_CB_Op118Transport
