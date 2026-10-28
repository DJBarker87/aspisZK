import NDO_JFu_TerminalPrefix
import NDO_JGl_WordProof
import NDO_JGl_NumericData
import RPv_FJa_TensorMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_TensorHigh0
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (0+i.val)=
      decoded JGl_NumericData.high ⟨0+i.val,by change 0+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh0
namespace AspisR1.JGl_TensorHigh1
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (8+i.val)=
      decoded JGl_NumericData.high ⟨8+i.val,by change 8+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh1
namespace AspisR1.JGl_TensorHigh2
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (16+i.val)=
      decoded JGl_NumericData.high ⟨16+i.val,by change 16+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh2
namespace AspisR1.JGl_TensorHigh3
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (24+i.val)=
      decoded JGl_NumericData.high ⟨24+i.val,by change 24+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh3
namespace AspisR1.JGl_TensorHigh4
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (32+i.val)=
      decoded JGl_NumericData.high ⟨32+i.val,by change 32+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh4
namespace AspisR1.JGl_TensorHigh5
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (40+i.val)=
      decoded JGl_NumericData.high ⟨40+i.val,by change 40+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh5
namespace AspisR1.JGl_TensorHigh6
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (48+i.val)=
      decoded JGl_NumericData.high ⟨48+i.val,by change 48+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh6
namespace AspisR1.JGl_TensorHigh7
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.take 6 |>.map decode) (56+i.val)=
      decoded JGl_NumericData.high ⟨56+i.val,by change 56+i.val<64;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorHigh7
namespace AspisR1.JGl_TensorLow0
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.drop 6 |>.map decode) (0+i.val)=
      decoded JGl_NumericData.low ⟨0+i.val,by change 0+i.val<16;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorLow0
namespace AspisR1.JGl_TensorLow1
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
/-- Eight bounded tensor cells, each a product of at most six coordinates.
Word-level operations are individually kernel checked. -/
theorem value (i : Fin 8) :
    FJa_TensorMeaning.weight (JFu_TerminalPrefix.alpha.val.drop 6 |>.map decode) (8+i.val)=
      decoded JGl_NumericData.low ⟨8+i.val,by change 8+i.val<16;omega⟩ := by
  fin_cases i <;> jgl_words
#print axioms value
end AspisR1.JGl_TensorLow1
end
