import R1Z.PV_RDEAC_ActualDigits
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_RoundValue
open PV_RDEAC_DigitText PV_RDEAC_ActualDigits PV_CBL_StringBytesAdapter
variable [ExternalTypes]

theorem text_length (i : Fin 16) : (encodeList (text i)).length=1 := by
  rw [←bytes,length]

theorem selected (ops : ExternalFuns) (digest : Array U8 32#usize)
    (s : String) (i : Usize) (h : i.val<digest.val.length)
    (bound : (encodeList s).length+2≤Usize.max) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    let b := digest.val[i.val]'h
    PV_RDEA_ActualNameLoop.round digest s i=ok ((s++text (high b))++text (low b)) := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  dsimp only
  rw [PV_RDEAC_ActualRound.factor,PV_RDEAC_ActualDigits.complete digest i h]
  simp only [bind_tc_ok]
  change (do
    let next ← append s (entry (high (digest.val[i.val]'h)))
    append next (entry (low (digest.val[i.val]'h))))=_
  rw [PV_RDEAC_AppendSimulation.callback_value s _ _ (bytes _) (by rw [length]; omega)]
  simp only [bind_tc_ok]
  apply PV_RDEAC_AppendSimulation.callback_value
  · exact bytes _
  · rw [PV_RDEAC_AppendSimulation.encode_append,List.length_append,text_length,length]
    omega

#print axioms text_length
#print axioms selected
end R1Z.PV_RDEAC_RoundValue
