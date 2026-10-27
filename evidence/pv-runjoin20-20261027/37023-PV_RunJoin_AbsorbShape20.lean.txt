import R1Z.PV_RunJoin_PartsBlock20
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AbsorbShape20
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem sponge (chunk : Array U32 8#usize) (len : Usize) (target : Array U32 16#usize)
    (h : ∀ j, j < 16 → (if j < 8 ∧ j < len.val then chunk.val[j]! else 0#u32) = target.val[j]!) :
    R0BlockCopies.sponge_absorb chunk len = ok target := by
  obtain ⟨ab,ha,hv⟩ := sponge_absorb_spec chunk len
  have he : ab = target := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    exact (hv j).trans (h j (by simpa using hj))
  exact ha.trans (congrArg Result.ok he)
#print axioms sponge
end R1Z.PV_RunJoin_AbsorbShape20
