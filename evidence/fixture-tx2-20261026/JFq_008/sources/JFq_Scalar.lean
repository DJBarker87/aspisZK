import JFq_Raw
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Scalar
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem k (pos : Usize) (b : Array U8 16#usize)
    (q : OraclePortCkptAbi2Extracted.aspis_core.field.QM31)
    (raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader pos)=
      ok (b,JFq_Raw.reader (Usize.wrapping_add pos 16#usize)))
    (decoded : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice b)=ok (some q)) :
    CheckpointBytes3Reader.readK (JFq_Raw.reader pos)=
      ok (.Ok (CheckpointBytes3Namespaces.fromK q),JFq_Raw.reader (Usize.wrapping_add pos 16#usize)) := by
  simp only [CheckpointBytes3Reader.readK,raw,bind_tc_ok,decoded,CheckpointBytes3Reader.optionK]

theorem e (pos : Usize) (b : Array U8 32#usize)
    (q : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact)
    (raw : CheckpointBytes3Reader.raw 32#usize (JFq_Raw.reader pos)=
      ok (b,JFq_Raw.reader (Usize.wrapping_add pos 32#usize)))
    (decoded : OraclePortCkptAbi2Extracted.decode_e_spec (Array.to_slice b)=ok (some q)) :
    CheckpointBytes3Reader.readE (JFq_Raw.reader pos)=
      ok (.Ok (CheckpointBytes3Namespaces.fromE q),JFq_Raw.reader (Usize.wrapping_add pos 32#usize)) := by
  simp only [CheckpointBytes3Reader.readE,raw,bind_tc_ok,decoded,CheckpointBytes3Reader.optionE]

#print axioms k
#print axioms e
end AspisR1.JFq_Scalar
end
