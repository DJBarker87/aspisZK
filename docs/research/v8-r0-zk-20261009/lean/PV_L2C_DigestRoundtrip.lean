import PV_L2C_DigestEncode
set_option autoImplicit false
namespace PV_L2C_DigestRoundtrip
open Aeneas Aeneas.Std Result R0Z.WriterRefine AspisR1TerminalDecoder

theorem decode (d : Array U32 8#usize) (hd : Canon8 d) :
    atomic_statement.decode_digest_canonical (PV_L2C_DigestEncode.encode d) = ok (.Ok d) := by
  have h0 := PV_L2C_DigestEncode.scalar d hd 0 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[0]!,(PV_L2C_DigestEncode.encode d).val[1]!,(PV_L2C_DigestEncode.encode d).val[2]!,(PV_L2C_DigestEncode.encode d).val[3]!]) = ok (some d.val[0]!) at h0
  have h1 := PV_L2C_DigestEncode.scalar d hd 1 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[4]!,(PV_L2C_DigestEncode.encode d).val[5]!,(PV_L2C_DigestEncode.encode d).val[6]!,(PV_L2C_DigestEncode.encode d).val[7]!]) = ok (some d.val[1]!) at h1
  have h2 := PV_L2C_DigestEncode.scalar d hd 2 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[8]!,(PV_L2C_DigestEncode.encode d).val[9]!,(PV_L2C_DigestEncode.encode d).val[10]!,(PV_L2C_DigestEncode.encode d).val[11]!]) = ok (some d.val[2]!) at h2
  have h3 := PV_L2C_DigestEncode.scalar d hd 3 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[12]!,(PV_L2C_DigestEncode.encode d).val[13]!,(PV_L2C_DigestEncode.encode d).val[14]!,(PV_L2C_DigestEncode.encode d).val[15]!]) = ok (some d.val[3]!) at h3
  have h4 := PV_L2C_DigestEncode.scalar d hd 4 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[16]!,(PV_L2C_DigestEncode.encode d).val[17]!,(PV_L2C_DigestEncode.encode d).val[18]!,(PV_L2C_DigestEncode.encode d).val[19]!]) = ok (some d.val[4]!) at h4
  have h5 := PV_L2C_DigestEncode.scalar d hd 5 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[20]!,(PV_L2C_DigestEncode.encode d).val[21]!,(PV_L2C_DigestEncode.encode d).val[22]!,(PV_L2C_DigestEncode.encode d).val[23]!]) = ok (some d.val[5]!) at h5
  have h6 := PV_L2C_DigestEncode.scalar d hd 6 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[24]!,(PV_L2C_DigestEncode.encode d).val[25]!,(PV_L2C_DigestEncode.encode d).val[26]!,(PV_L2C_DigestEncode.encode d).val[27]!]) = ok (some d.val[6]!) at h6
  have h7 := PV_L2C_DigestEncode.scalar d hd 7 (by omega)
  change aspis_core.field.M31.from_le_bytes (Array.make 4#usize [(PV_L2C_DigestEncode.encode d).val[28]!,(PV_L2C_DigestEncode.encode d).val[29]!,(PV_L2C_DigestEncode.encode d).val[30]!,(PV_L2C_DigestEncode.encode d).val[31]!]) = ok (some d.val[7]!) at h7
  unfold atomic_statement.decode_digest_canonical
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 0#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 1#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 2#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 3#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 4#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 5#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 6#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 7#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 8#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 9#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 10#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 11#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 12#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 13#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 14#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 15#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 16#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 17#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 18#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 19#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 20#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 21#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 22#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 23#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 24#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 25#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 26#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 27#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 28#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 29#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 30#usize (by scalar_tac)]
  rw [index_ok_gen (PV_L2C_DigestEncode.encode d) 31#usize (by scalar_tac)]
  simp only [bind_tc_ok,UScalar.ofNatCore_val_eq]
  rw [h0]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h1]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h2]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h3]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h4]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h5]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h6]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  rw [h7]
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  congr 2
  apply R1Z.BuilderRecordCanonical.array_ext
  intro j hj
  have hj' : j < 8 := by simpa using hj
  interval_cases j <;> rfl
#print axioms decode

theorem origin (d : Array U32 8#usize) (hd : Canon8 d) : PV_L2C_DigestOrigin.Origin d :=
  .decoded (PV_L2C_DigestEncode.encode d) (decode d hd)
#print axioms origin
end PV_L2C_DigestRoundtrip
