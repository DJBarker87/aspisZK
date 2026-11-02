import R1Z.PV_RunJoin_FactoredParser73
import R1Z.PV_RunJoin_WireReaders73
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WideWireParse73
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FlatBytes35 (wire)

theorem complete (x : aspis_core.field.wide_exact.WideExact)
    (canonical : PV_RunJoin_WideLimbsParse72.Canonical x) :
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes
      (Array.to_slice (wire x))=ok (some x) := by
  rw [PV_RunJoin_FactoredParser73.source]
  have size : Slice.len (Array.to_slice (wire x))=32#usize := by
    apply UScalar.eq_of_val_eq
    exact (wire x).property
  unfold PV_RunJoin_FactoredParser73.parse
  rw [size]
  simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_WireReaders73.word0];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word1];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word2];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word3];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word4];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word5];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word6];simp only [bind_tc_ok]
  rw [PV_RunJoin_WireReaders73.word7];simp only [bind_tc_ok]
  exact PV_RunJoin_WideLimbsParse72.complete x canonical

#print axioms complete
end R1Z.PV_RunJoin_WideWireParse73
