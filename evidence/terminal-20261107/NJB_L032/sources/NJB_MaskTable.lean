import CopyActiveMaskBasisRegroup
set_option autoImplicit false
namespace AspisR1.NJB_MaskTable
/-- Exact frozen Rust u16 table; SHA and extraction retained in NJB_MASK_TABLE.json. -/
def nativeMasks : Fin 64 → Nat := ![6144,6144,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6144,4097,2048,6145,2049,2048,6145,2049,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,4097,6145,6145,4097,26214,26214,26214,26214,26214,26214,1749]
theorem source_eq_model (b : Fin 64) : nativeMasks b=R0P.copyActiveRowMasks b := by
 fin_cases b <;> decide
theorem source_key_eq_model (b : Fin 64) :
 R0P.activeMaskCoordinate (nativeMasks b)=R0P.activeMaskCoordinate (R0P.copyActiveRowMasks b) := by
 rw [source_eq_model]
#print axioms source_eq_model
#print axioms source_key_eq_model
end AspisR1.NJB_MaskTable
