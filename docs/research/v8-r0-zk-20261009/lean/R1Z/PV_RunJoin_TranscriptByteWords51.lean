import R1Z.PV_RunJoin_OpeningByteCodec51
import R1Z.ProverCommitSaltBytes
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TranscriptByteWords51
open Aeneas Aeneas.Std
open ProverCommitOwnerBytes42 (byte)

theorem byte_salt (b : U8) : byte b=ProverCommitSaltBytes.byte b := by
  apply UInt8.toNat_inj.mp
  change b.val=b.val%256
  exact (Nat.mod_eq_of_lt b.bv.isLt).symm

theorem word (n : U32) : (core.num.U32.to_le_bytes n).val.map byte=TranscriptR1.le32 n.val := by
  have eq : byte=ProverCommitSaltBytes.byte := funext byte_salt
  rw [eq]
  exact ProverCommitSaltBytes.le32_source n

theorem cast32 (n : Usize) (h : n.val≤U32.max) : (UScalar.cast .U32 n).val=n.val := by
  scalar_tac

theorem tag (row : U8) : byte (U8.wrapping_add 160#u8 row)=160+byte row := by
  rfl
#print axioms byte_salt
#print axioms word
#print axioms cast32
#print axioms tag
end R1Z.PV_RunJoin_TranscriptByteWords51
