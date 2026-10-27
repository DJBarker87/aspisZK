import FJe_PackedRawRowValue
import FJb_LimbMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedInputWords
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical decoded)
open FJb_TailCell (cell)
open AspisV8R15.ExactTowerBase (P)
def mapped (a : Array NQ 4#usize) := FJb_ArrayTransport.array FJb_LimbMap.words a

theorem bounded (a : Array NQ 4#usize) (ha : canonical a) (r j : Fin 4) :
    FJe_PackedRawRowValue.words (mapped a) r j<P := by
  have hq : Canon (cell a r) := ha _ (List.getElem_mem (by simpa only [a.property] using r.isLt))
  fin_cases j
  · simpa only [FJe_PackedRawRowValue.words,mapped,FJb_ArrayTransport.array,
      List.getElem_map,FJb_LimbMap.words,Array.make,cell] using hq.1.1
  · simpa only [FJe_PackedRawRowValue.words,mapped,FJb_ArrayTransport.array,
      List.getElem_map,FJb_LimbMap.words,Array.make,cell] using hq.1.2
  · simpa only [FJe_PackedRawRowValue.words,mapped,FJb_ArrayTransport.array,
      List.getElem_map,FJb_LimbMap.words,Array.make,cell] using hq.2.1
  · simpa only [FJe_PackedRawRowValue.words,mapped,FJb_ArrayTransport.array,
      List.getElem_map,FJb_LimbMap.words,Array.make,cell] using hq.2.2

theorem decoded_value (a : Array NQ 4#usize) (r : Fin 4) :
    RawPoseidonRowField.decodeWords (FJe_PackedRawRowValue.words (mapped a) r)=decoded a r := by
  exact FJb_LimbMeaning.words a r
#print axioms bounded
#print axioms decoded_value
end AspisR1.FJe_PackedInputWords
end
