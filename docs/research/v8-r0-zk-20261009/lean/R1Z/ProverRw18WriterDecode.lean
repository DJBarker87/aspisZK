import R1Z.ProverRw18CodecDecode
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18WriterDecode
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
open AspisR1.RetainedFieldByteCodec

theorem exact_decode (x : Raw) (hx : Canonical x) (out : Slice U8) (length : out.val.length=16) :
    ∃ result : Slice U8,ProverRw18QuarticWrite.source (full x) out=ok result ∧
      decodeQM31Bytes (result.val.map ProverCommitWordBytes47.rawByte)=
        some (ProverCommitLimbBytes47.limbs x hx) := by
  obtain ⟨result,hr,hbytes⟩ := ProverRw18QuarticBytes.exact_write (full x) out (by omega)
  refine ⟨result,hr,?_⟩
  rw [hbytes,List.drop_eq_nil_iff.mpr (by omega : out.val.length≤16),List.append_nil]
  exact ProverRw18CodecDecode.canonical x hx

#print axioms exact_decode
end R1Z.ProverRw18WriterDecode
