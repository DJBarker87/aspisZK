import NDO_JFv_TX2_SlotMeaning
import NDO_JFs_TX2_Dots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_DotsMeaning
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
abbrev NE := FIo_Install.NE

theorem source (i : Fin 12) :
    ∃ head tail out : Fin 4 → NE,
      JFs_TX2_Dots.nativeValue i=Array.make 4#usize [out 0,out 1,out 2,out 3] ∧
      ∀ slot : Fin 4,
        JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
          (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok (tail slot) ∧
        FIo_WideValues.Canon (head slot) ∧ FIo_WideValues.Canon (tail slot) ∧ FIo_WideValues.Canon (out slot) ∧
        AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (out slot))=
          AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (head slot))+
          AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (tail slot)) ∧
        ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs (head slot)) j).val=
          JFv_TX2_InnerMeaning.sum i slot j 0 26%2147483647 := by
  have all := fun slot : Fin 4 => JFv_TX2_SlotMeaning.source i slot
  choose head tail out run ht ch ct co vo vh using all
  have r0 := run 0
  have r1 := run 1
  have r2 := run 2
  have r3 := run 3
  have c0 : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  have c1 : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  have c2 : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  have c3 : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [c0] at r0
  rw [c1] at r1
  rw [c2] at r2
  rw [c3] at r3
  have native : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value (JFn_Values.position i))
      JFr_TX2_FirstLane.native=ok (Array.make 4#usize [out 0,out 1,out 2,out 3]) := by
    rw [JFs_TX2_FourHead.source]
    simp only [JFs_TX2_FourHead.slots,r0,r1,r2,r3,bind_tc_ok]
  refine ⟨head,tail,out,Result.ok.inj ((JFs_TX2_Dots.native i).symm.trans native),?_⟩
  intro slot
  exact ⟨ht slot,ch slot,ct slot,co slot,vo slot,vh slot⟩
#print axioms source
end AspisR1.JFv_TX2_DotsMeaning
end
