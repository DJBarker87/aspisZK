import NHE_BytePort
set_option autoImplicit false
namespace NHE_FieldPort
open Aeneas Aeneas.Std Result AspisR1

theorem unwrap (o : Option FIo_Install.NE) :
 FIo_FieldBridge.map FIo_Install.fromE (core.option.Option.unwrap o)=
 (do let x ← core.option.Option.unwrap (Option.map NHE_ParsePort.record o)
     ok (SAG_DotAdapter.toStageE (AspisR1CurrentWide.Proof.recordWideToFinish x))) := by
 cases o <;> rfl

theorem decoder (bytes : Slice U8) :
 FIo_FieldBridge.map FIo_Install.fromE
   (do let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
       core.option.Option.unwrap o)=
 (do let o ← AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes
     let x ← core.option.Option.unwrap o
     ok (SAG_DotAdapter.toStageE (AspisR1CurrentWide.Proof.recordWideToFinish x))) := by
 rw [←NHE_BytePort.bytes,FIo_FieldBridge.map_bind]
 cases h : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes with
 | fail e => rfl
 | div => rfl
 | ok o => exact unwrap o

theorem adopted (bytes : Slice U8) (i : Usize) (small : i.val<64) :
 FIo_FieldBridge.map FIo_Install.fromE (FIo_Native.weights.field bytes i)=
 FIn_Primitives.field bytes i := by
 have cap : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have hm := FIo_ScalarBridge.mul i 32#usize (by change i.val*32<UScalar.size .Usize;omega)
 have ha := FIo_ScalarBridge.add i 1#usize (by change i.val+1<UScalar.size .Usize;omega)
 have av : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt (by change i.val+1<UScalar.size .Usize;omega)]
 have hf := FIo_ScalarBridge.mul (Usize.wrapping_add i 1#usize) 32#usize (by change (Usize.wrapping_add i 1#usize).val*32<UScalar.size .Usize;rw [av];omega)
 simp only [FIo_Native.weights.field,FIn_Primitives.field,AspisR1CurrentWide.Proof.finishField,AspisR1WeightsFieldCurrent.weights.field,hm,ha,hf,lift,bind_tc_ok,FIo_FieldBridge.map_bind,bind_assoc_eq]
 congr 1
 funext selected
 exact decoder selected

#print axioms unwrap
#print axioms decoder
#print axioms adopted
end NHE_FieldPort
