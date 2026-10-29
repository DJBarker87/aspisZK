import R1Z.PV_RDEAC_NameText
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_NameValue
open PV_RDEAC_NameText PV_RDEAC_DigitText PV_RDEAC_ActualDigits PV_CBL_StringBytesAdapter
variable [ExternalTypes]

theorem five_bytes (bs : ByteArray) (h : bs.size=5) :
    bs.toList=[bs.get! 0,bs.get! 1,bs.get! 2,bs.get! 3,bs.get! 4] := by
  unfold ByteArray.toList
  rw [ByteArray.toList.loop]
  simp only [h,show (0 : Nat)<5 from by decide,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,show (1 : Nat)<5 from by decide,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,show (2 : Nat)<5 from by decide,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,show (3 : Nat)<5 from by decide,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,show (4 : Nat)<5 from by decide,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,show ¬(5 : Nat)<5 from by decide,if_false]
  rfl

theorem suffix : PV_RDEA_ActualReservation.suffixText.val=encodeList ".burn" := by
  unfold PV_RDEA_ActualReservation.suffixText toStr
  change (".burn".toByteArray.toList.map encodeByte)=encodeList ".burn"
  rw [five_bytes _ (by rw [String.size_toByteArray]; rfl)]
  rfl

theorem finite (ops : ExternalFuns) (digest : Array U8 32#usize)
    (n : Nat) (s : String) (i : Usize) (endpoint : i.val+n=32)
    (bound : (encodeList s).length+2*n+5≤Usize.max) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    PV_RDEA_ActualNameLoop.finite digest n s i=ok (s++basenameText (digest.val.drop i.val)) := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  have length : digest.val.length=32 := digest.property
  induction n generalizing s i with
  | zero =>
    have endIndex : digest.val.length ≤ i.val := by omega
    rw [List.drop_eq_nil_iff.mpr endIndex]
    change append s PV_RDEA_ActualReservation.suffixText=ok (s++".burn")
    apply PV_RDEAC_AppendSimulation.callback_value s ".burn" _ suffix
    have hl : PV_RDEA_ActualReservation.suffixText.val.length=5 := by rw [suffix,suffix_bytes]; rfl
    rw [hl]
    omega
  | succ n ih =>
    have hi : i.val<digest.val.length := by omega
    have add : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      apply Nat.mod_eq_of_lt
      have large := (32#usize).hSize
      change 32<UScalar.size .Usize at large
      omega
    rw [PV_RDEA_ActualNameLoop.finite,PV_RDEAC_RoundValue.selected ops digest s i hi (by omega)]
    simp only [bind_tc_ok]
    rw [ih ((s++text (high (digest.val[i.val]'hi)))++text (low (digest.val[i.val]'hi)))
      (Usize.wrapping_add i 1#usize) (by omega) (by
        simp only [PV_RDEAC_AppendSimulation.encode_append,List.length_append,
          PV_RDEAC_RoundValue.text_length]
        omega)]
    rw [add,List.drop_eq_getElem_cons hi]
    simp only [basenameText,String.append_assoc]

theorem start (ops : ExternalFuns) (digest : Array U8 32#usize)
    (s : String) (bound : (encodeList s).length+69≤Usize.max) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    aspis_prover.state_only_entropy.reservation_name digest s 0#usize=
      ok (s++basenameText digest.val) := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  rw [PV_RDEA_ActualNameFinite.start,finite ops digest 32 s 0#usize rfl (by omega)]
  rfl

#print axioms five_bytes
#print axioms suffix
#print axioms finite
#print axioms start
end R1Z.PV_RDEAC_NameValue
