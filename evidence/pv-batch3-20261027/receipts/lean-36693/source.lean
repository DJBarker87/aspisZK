import PV_B3_ArrayUpdateCarrier
import PV_B3_FieldTransport
namespace PV_B3_QArrayCarrier
open Aeneas Aeneas.Std Result PV_B3_ArrayCarrier PV_B3_FieldTransport
set_option autoImplicit false

def toArray {n : Usize} (a : Array New.Q n) : Array Old.Q n := arrayMap toQ a
def fromArray {n : Usize} (a : Array Old.Q n) : Array New.Q n := arrayMap fromQ a

theorem left {n : Usize} (a : Array New.Q n) : fromArray (toArray a) = a :=
  inverse toQ fromQ q_left a

theorem right {n : Usize} (a : Array Old.Q n) : toArray (fromArray a) = a :=
  inverse fromQ toQ q_right a

theorem index_to {n : Usize} (a : Array New.Q n) (i : Usize) :
    Array.index_usize (toArray a) i = resultMap toQ (Array.index_usize a i) := index toQ a i

theorem update_to {n : Usize} (a : Array New.Q n) (i : Usize) (x : New.Q) :
    resultMap toArray (Array.update a i x) = Array.update (toArray a) i (toQ x) :=
  PV_B3_ArrayUpdateCarrier.update toQ a i x

#print axioms toArray
#print axioms fromArray
#print axioms left
#print axioms right
#print axioms index_to
#print axioms update_to
end PV_B3_QArrayCarrier
