import RPv_FJb_LimbMap
import RPv_FJb_RawRowValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_LimbMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (decoded)
theorem words (a : Array NQ 4#usize) (i : Fin (4#usize).val) :
    RawPoseidonRowField.decodeWords (RawPoseidonExternalRowExact.inputWords
      (FJb_ArrayTransport.array FJb_LimbMap.words a) i)=decoded a i := by
  simp only [RawPoseidonRowField.decodeWords,RawPoseidonExternalRowExact.inputWords,
    RawPoseidonExternalRowReads.rowValue,FJb_ArrayTransport.array,List.getElem_map,
    FJb_LimbMap.words,Array.make,decoded,FIw_ArrayValue.cells]
  rfl
/-- Value of one native matrix row after the SAME actual map of four inputs. -/
theorem value (a : Array NQ 4#usize) (input : Array (Array U32 4#usize) 4#usize)
    (output : Usize) (ho : output.val < 4) (out : NQ)
    (mapped : FIq_Native.core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize))
      a state_only_poseidon.extension_limbs=ok input)
    (run : state_only_poseidon.external_linear_lazy_row input output=ok out) :
    Canon out ∧ decode out=R0P.poseidonMat4 (decoded a) ⟨output.val,ho⟩ := by
  have eq := FJb_LimbMap.value a input mapped
  subst input
  have v := FJb_RawRowValue.value _ output ho out run
  refine ⟨v.1,?_⟩
  have he : (fun i=>RawPoseidonRowField.decodeWords
      (RawPoseidonExternalRowExact.inputWords (FJb_ArrayTransport.array FJb_LimbMap.words a) i))=
      decoded a := by funext i;exact words a i
  rw [he] at v
  exact v.2
#print axioms words
#print axioms value
end AspisR1.FJb_LimbMeaning
end
