import SAQ_Decoder
import NFS_ReadCanonical
import CurrentCallerUsizeArithmeticV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_ReadTransport
open Aeneas Aeneas.Std Result

theorem ite_bind {α β : Type} (c : Prop) [Decidable c] (a b : Result α) (f : α → Result β) :
 ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
 split <;> rfl

/-- Wrapping index arithmetic on the reached indices (no overflow). -/
theorem wmul (x : Usize) (hx : x.val < 8) : (Usize.wrapping_mul x 32#usize).val = x.val * 32 := by
 have h32 : (32#usize).val = 32 := by scalar_tac
 have cap : x.val * 32 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
 rw [Usize.wrapping_mul_val_eq, h32, Nat.mod_eq_of_lt cap]

theorem wadd (x : Usize) (hx : x.val < 8) : (Usize.wrapping_add x 1#usize).val = x.val + 1 := by
 have h1 : (1#usize).val = 1 := by scalar_tac
 have cap : x.val + 1 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
 rw [Usize.wrapping_add_val_eq, h1, Nat.mod_eq_of_lt cap]

/-- The checked (SAQ) and wrapping (FIo) window computations agree on i < 4. -/
theorem start (i : Usize) (hi : i.val < 4) :
 (32#usize * i : Result Usize) = ok (Usize.wrapping_mul i 32#usize) :=
 AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok _ _ _
  (by rw [wmul i (by omega)]; scalar_tac) (by scalar_tac)

theorem finish (i : Usize) (hi : i.val < 4) :
 (Usize.wrapping_mul i 32#usize + 32#usize : Result Usize) =
 ok (Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize) :=
 AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok _ _ _
  (by rw [wmul i (by omega), wmul _ (by rw [wadd i (by omega)]; omega), wadd i (by omega)]; scalar_tac)
  (by rw [wmul i (by omega)]; scalar_tac)

/-- X2 core: the two extracted canonical wide-field decoders are the SAME full
Result on every 32-byte-aligned opening index i < 4 (any byte content). -/
theorem read (bytes : Slice U8) (i : Usize) (hi : i.val < 4) :
 SAQ_Decoder.read bytes i = NFS_ReadCanonical.read bytes i := by
 unfold SAQ_Decoder.read NFS_ReadCanonical.read FIo_Native.weights.field
 simp only [start i hi, finish i hi, lift, bind_tc_ok, bind_assoc_eq, ite_bind,
  AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes,
  AspisR1RecordParser.field.wide_exact.WideExact.from_limbs,
  FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
  FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
  AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN,
  FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
  AspisR1RecordParser.field.P, FIo_Native.aspis_core.field.P,
  core.option.Option.unwrap, AspisR1.SAQ_RecordDecode.fromRecord, AspisR1.FIo_Install.fromE]
#print axioms wmul
#print axioms wadd
#print axioms start
#print axioms finish
#print axioms read
end AspisR1.NOC_ReadTransport
end
