import PV_B3Q_ArrayBorrow
import PV_B3Q_ArrayView
import PV_B3Q_BitCounts
import PV_B3Q_ByteArrayEq
import PV_B3Q_CheckedAdd
import PV_B3Q_CloneActual
import PV_B3Q_CompareActual
import PV_B3Q_D188
import PV_B3Q_FormatLiteral
import PV_B3Q_FourSlice
import PV_B3Q_Iterator4
import PV_B3Q_IteratorAlignment
import PV_B3Q_M31SliceActual
import PV_B3Q_MatrixEntries
import PV_B3Q_MatrixFrame
import PV_B3Q_MatrixIntermediate
import PV_B3Q_MatrixStore
import PV_B3Q_MatrixTrace
import PV_B3Q_OptionEquality
import PV_B3Q_Range
import PV_B3Q_ResultResidual
import PV_B3Q_ScalarEquality
import PV_B3Q_SliceActual
import PV_B3Q_SliceEqual
import PV_B3Q_SliceEqualityValue
import PV_B3Q_SliceSuffix
import PV_B3Q_StdPartial
import PV_B3Q_StdValues
import PV_B3Q_Wrapping
namespace PV_B3Q_Combined
open Aeneas Aeneas.Std PV_B3P_Groups14227 PV_B3P_Binding14227
set_option autoImplicit false
/-- Joint non-vacuity for these explicit, partial source ports. This is not a
complete deployed catalogue or a new callback/endpoint decomposition. -/
theorem joint_scope_witness :
    ∃ (store : Store14)
      (matrixStore : Matrix14 → Usize → Usize → U64 → Result Matrix14)
      (slice : SliceFn14),
      PV_B3P_Link_D188 store ∧ PV_B3P_Link_matrix_stores matrixStore ∧
      PV_B3P_Link_slice14 slice ∧
      PV_B3P_Link_std_dependency_closure14 (PV_B3Q_Std.Signature Unit Unit)
        (PV_B3Q_Std.native Unit Unit) (PV_B3Q_Std.model Unit Unit) :=
 ⟨PV_B3Q_D188.direct_store,PV_B3Q_Matrix.deployed_store,PV_B3Q_FourSlice.source,
   PV_B3Q_D188.direct_store_link,PV_B3Q_Matrix.deployed_store_link,
   PV_B3Q_FourSlice.source_link,PV_B3Q_Std.partial_catalogue_link Unit Unit⟩
#print axioms joint_scope_witness
end PV_B3Q_Combined
