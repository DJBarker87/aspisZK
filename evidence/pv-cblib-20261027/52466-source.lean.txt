import R1Z.PV_CBL_SoftByteExtracted
import R1Z.PV_CBL_Suffix64Value
import R1Z.PV_CBL_DigestBytesValue
import R1Z.PV_CBL_PadContentSource
import R1Z.PV_CBL_ShaBitLength
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FinalizeSoftValue
set_option autoImplicit false
def next (state : Array U32 8#usize) (first : Array U8 64#usize)
    (second : Option (Array U8 64#usize)) : Array U32 8#usize :=
  let initial := PV_CBL_SoftByteSource.value state first
  match second with
  | none => initial
  | some b => PV_CBL_SoftByteSource.value initial b
/-- Complete value result of the fixed owned soft finalizer, including retained
padding contents. Native generic wrapper/loan/Drop and dispatch are separate. -/
theorem source (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    ∃ first second,
      PV_CBL_FinalSoft.sha_finalize_soft_owned state blocks buffer pos =
        ok (PV_CBL_DigestBytesValue.value (next state first second),
            next state first second,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val
        (PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)).val ∧
      second.map (fun a => a.val) = PV_CBL_PaddingModel.second pos.val
        (PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)).val := by
  obtain ⟨first,second,hpad,hfirst,hsecond⟩ := PV_CBL_PadContentSource.source buffer pos
    (PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)) hp
  have hbits : PV_CBL_ShaBitLength.bitLength pos blocks =
      core.num.U64.wrapping_mul 8#u64
        (core.num.U64.wrapping_add (UScalar.cast .U64 pos) (core.num.U64.wrapping_mul 64#u64 blocks)) := rfl
  rw [hbits] at hpad
  refine ⟨first,second,?_,hfirst,hsecond⟩
  unfold PV_CBL_FinalSoft.sha_finalize_soft_owned
  simp only [lift,bind_tc_ok,PV_CBL_Suffix64Value.source]
  rw [hpad,bind_tc_ok]
  cases second <;> simp only [PV_CBL_SoftByteExtracted.source,bind_tc_ok,PV_CBL_DigestBytesValue.source,next] <;> rfl
#print axioms next
#print axioms source
end R1Z.PV_CBL_FinalizeSoftValue
