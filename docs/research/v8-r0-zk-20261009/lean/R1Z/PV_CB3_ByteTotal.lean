import R1Z.PV_CB3_Op51Arbitrary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_ByteTotal
open Aeneas Aeneas.Std Result ProverRwFull
/-- The flat source cannot fail or diverge, even for noncanonical field words. -/
theorem total (x : aspis_core.field.wide_exact.WideExact) :
    ∃ bytes, PV_CB3_Op51Source.Raw.wide_bytes_flat x = ok bytes := by
  simp [PV_CB3_Op51Source.Raw.wide_bytes_flat,
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs,
    lift, bind_tc_ok, Array.index_usize, Array.make, core.num.U32.to_le_bytes, BitVec.toLEBytes]
#print axioms total
end R1Z.PV_CB3_ByteTotal
