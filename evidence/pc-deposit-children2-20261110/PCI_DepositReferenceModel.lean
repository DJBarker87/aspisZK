import PCI_DepositWords
import PCI_ArrayCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositReferenceModel

def model (h : Array U8 80#usize) (len : Usize) (magic : Array U8 4#usize) : Result PCI_DepositRef.Decoded := do
 if len<80#usize then PCI_DepositRef.error 1#u8
 else if len>592#usize then PCI_DepositRef.error 1#u8
 else
  let bad ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    (Array.make 4#usize [h.val[0]!,h.val[1]!,h.val[2]!,h.val[3]!]) magic
  if bad then PCI_DepositRef.error 2#u8
  else if h.val[4]! != 1#u8 then PCI_DepositRef.error 3#u8
  else if h.val[5]! != 0#u8 then PCI_DepositRef.error 4#u8
  else
   let reserved ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    (Array.make 4#usize [h.val[44]!,h.val[45]!,h.val[46]!,h.val[47]!]) (Array.repeat 4#usize 0#u8)
   if reserved then PCI_DepositRef.error 4#u8
   else
    let declared := UScalar.cast .Usize (core.num.U16.from_le_bytes
      (Array.make 2#usize [h.val[6]!,h.val[7]!]))
    if declared>512#usize then PCI_DepositRef.error 6#u8
    else
     let last ← 80#usize+declared
     if len != last then PCI_DepositRef.error 1#u8
     else
      let owner := PCI_DepositWords.model h 8
      if PCI_ArrayCanonical.model owner then
       let salt := PCI_DepositWords.model h 48
       if PCI_ArrayCanonical.model salt then
        let amount := PCI_DepositRead.model_word h 40
        if amount=0#u32 then PCI_DepositRef.error 5#u8
        else if amount>=1073741824#u32 then PCI_DepositRef.error 5#u8
        else
         let payload_len ← len-80#usize
         ok {tag:=0#u8,owner,amount,salt,payload_len}
       else PCI_DepositRef.error 7#u8
      else PCI_DepositRef.error 7#u8

theorem extracted (h : Array U8 80#usize) (len : Usize) (magic : Array U8 4#usize) :
    PCI_DepositRef.decode_reference h len magic=model h len magic := by
 unfold PCI_DepositRef.decode_reference model
 simp only [PCF_ArrayIndex.result h 0#usize (by scalar_tac),PCF_ArrayIndex.result h 1#usize (by scalar_tac),PCF_ArrayIndex.result h 2#usize (by scalar_tac),PCF_ArrayIndex.result h 3#usize (by scalar_tac),PCF_ArrayIndex.result h 4#usize (by scalar_tac),PCF_ArrayIndex.result h 5#usize (by scalar_tac),PCF_ArrayIndex.result h 6#usize (by scalar_tac),PCF_ArrayIndex.result h 7#usize (by scalar_tac),PCF_ArrayIndex.result h 44#usize (by scalar_tac),PCF_ArrayIndex.result h 45#usize (by scalar_tac),PCF_ArrayIndex.result h 46#usize (by scalar_tac),PCF_ArrayIndex.result h 47#usize (by scalar_tac),PCI_DepositWords.words h 8#usize (by scalar_tac),PCI_DepositWords.words h 48#usize (by scalar_tac),PCI_DepositRead.word h 40#usize (by scalar_tac),PCI_ArrayCanonical.extracted,bind_tc_ok,lift,pure]
 rfl

#print axioms extracted
end PCI_DepositReferenceModel
