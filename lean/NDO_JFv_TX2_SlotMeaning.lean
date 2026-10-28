import NDO_JFv_TX2_HeadFlat
import NDO_JFs_TX2_Slot
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_SlotMeaning
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)

theorem factor (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) (slot : Usize) :
    FIp_NativeDots.fast_dots.four_dots_one q g slot=
      (do let head ← JFs_TX2_ScalarHead.sourceCall q g slot
          let tail ← JFs_TX2_DotSuffix.tail q g slot
          FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail) := by
  rw [JFs_TX2_DotSuffix.body]
  simp only [JFs_TX2_ScalarHead.sourceCall,bind_assoc_eq,bind_tc_ok]

theorem source (i : Fin 12) (slot : Fin 4) :
    ∃ head tail out,
      FIp_NativeDots.fast_dots.four_dots_one
        (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧
      JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok tail ∧
      FIo_WideValues.Canon head ∧ FIo_WideValues.Canon tail ∧ FIo_WideValues.Canon out ∧
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide out)=
        AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide head)+
        AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide tail) ∧
      ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs head) j).val=
        JFv_TX2_InnerMeaning.sum i slot j 0 26%2147483647 := by
  obtain ⟨head,hhead,ch,values⟩ := JFv_TX2_HeadFlat.source i slot
  obtain ⟨tail,ht,ct⟩ := JFs_TX2_TailTotal.source i slot JFr_TX2_FirstLane.native
  obtain ⟨out,add,canon⟩ := JFs_TX2_WideAdd.source head tail ch ct
  have value := (FIo_WideValues.add head tail out ch ct add).2
  refine ⟨head,tail,out,?_,ht,ch,ct,canon,value,values⟩
  rw [factor,hhead,bind_tc_ok,ht,bind_tc_ok,add]
#print axioms factor
#print axioms source
end AspisR1.JFv_TX2_SlotMeaning
end
