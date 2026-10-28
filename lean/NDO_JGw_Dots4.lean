import NDO_JGw_Scalars4
import NDO_JGw_Tails04
import NDO_JGw_DotTotal
import NDO_JFs_TX2_FourHead
import RPt_FIp_DotsAllCanonical
import RPt_FIp_DotsOutputCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Dots4
open Aeneas Aeneas.Std Result

def q : Array U8 608#usize := JFr_TX2_Windows.array ⟨4,by decide⟩
def scalar (slot : Fin 4) (term : Fin 26) : U32 := match slot.val with
  | 0 => JGw_Slot04_0.values.val[term.val]'(by rw [JGw_Slot04_0.values.property];exact term.isLt)
  | 1 => JGw_Slot04_1.values.val[term.val]'(by rw [JGw_Slot04_1.values.property];exact term.isLt)
  | 2 => JGw_Slot04_2.values.val[term.val]'(by rw [JGw_Slot04_2.values.property];exact term.isLt)
  | _ => JGw_Slot04_3.values.val[term.val]'(by rw [JGw_Slot04_3.values.property];exact term.isLt)

theorem reads (slot : Fin 4) (term : Fin 26) :
    JFr_TX2_ScalarRead.read q (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))=ok (scalar slot term) := by
  fin_cases slot
  · exact JGw_Slot04_0.source term
  · exact JGw_Slot04_1.source term
  · exact JGw_Slot04_2.source term
  · exact JGw_Slot04_3.source term
#print axioms reads

theorem canonical (slot : Fin 4) (term : Fin 26) : (scalar slot term).val<2147483647 := by
  fin_cases slot
  · exact JFr_TX2_ScalarCanon.source _ _ (JGw_Slot04_0.decode term)
  · exact JFr_TX2_ScalarCanon.source _ _ (JGw_Slot04_1.decode term)
  · exact JFr_TX2_ScalarCanon.source _ _ (JGw_Slot04_2.decode term)
  · exact JFr_TX2_ScalarCanon.source _ _ (JGw_Slot04_3.decode term)
#print axioms canonical

theorem tail0 (slot : Fin 4) :
    ∃ v, JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 0) (JFr_TX2_Tails.stop slot 0)=ok v := by
  fin_cases slot
  · exact ⟨_,JGw_Tails04.source0_0⟩
  · exact ⟨_,JGw_Tails04.source0_1⟩
  · exact ⟨_,JGw_Tails04.source0_2⟩
  · exact ⟨_,JGw_Tails04.source0_3⟩
#print axioms tail0

theorem tail1 (slot : Fin 4) :
    ∃ v, JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 1) (JFr_TX2_Tails.stop slot 1)=ok v := by
  fin_cases slot
  · exact ⟨_,JGw_Tails04.source1_0⟩
  · exact ⟨_,JGw_Tails04.source1_1⟩
  · exact ⟨_,JGw_Tails04.source1_2⟩
  · exact ⟨_,JGw_Tails04.source1_3⟩
#print axioms tail1

theorem tail2 (slot : Fin 4) :
    ∃ v, JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 2) (JFr_TX2_Tails.stop slot 2)=ok v := by
  fin_cases slot
  · exact ⟨_,JGw_Tails04.source2_0⟩
  · exact ⟨_,JGw_Tails04.source2_1⟩
  · exact ⟨_,JGw_Tails04.source2_2⟩
  · exact ⟨_,JGw_Tails04.source2_3⟩
#print axioms tail2

theorem slot (j : Fin 4) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one q JFr_TX2_FirstLane.native
      (Usize.ofNat j.val (by have:=j.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨q0,h0⟩ := tail0 j
  obtain ⟨q1,h1⟩ := tail1 j
  obtain ⟨q2,h2⟩ := tail2 j
  exact JGw_DotTotal.source q j (scalar j) (reads j) (canonical j) q0 q1 q2 h0 h1 h2
#print axioms slot

theorem native :
    ∃ out, FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨4,by decide⟩)
      JFr_TX2_FirstLane.native=ok out ∧ FIo_ArrayCanon.Holds out := by
  obtain ⟨a,h0,_⟩ := slot 0
  have z0 : Usize.ofNat ((0:Fin 4).val) (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z0] at h0
  obtain ⟨b,h1,_⟩ := slot 1
  have z1 : Usize.ofNat ((1:Fin 4).val) (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z1] at h1
  obtain ⟨c,h2,_⟩ := slot 2
  have z2 : Usize.ofNat ((2:Fin 4).val) (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z2] at h2
  obtain ⟨d,h3,_⟩ := slot 3
  have z3 : Usize.ofNat ((3:Fin 4).val) (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z3] at h3
  let out : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,b,c,d]
  have run : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨4,by decide⟩)
      JFr_TX2_FirstLane.native=ok out := by
    rw [JFs_TX2_FourHead.source]
    change JFs_TX2_FourHead.slots q JFr_TX2_FirstLane.native=ok out
    simp only [JFs_TX2_FourHead.slots,h0,h1,h2,h3,bind_tc_ok]
    rfl
  exact ⟨out,run,FIp_DotsAllCanonical.four _ _ out run⟩
#print axioms native

def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray (Classical.choose native)

theorem source : FIp_DotsAdapter.dots (JFo_Opening.value ⟨4,by decide⟩)
    JFr_TX2_Powers.value=ok value := by
  change (do let out ← FIp_NativeDots.fast_dots.four_dots
               (JFo_Opening.value ⟨4,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok value
  rw [(Classical.choose_spec native).1,bind_tc_ok]
  rfl
#print axioms source

theorem output_canonical : ∀ x∈value.val, Port4C_QueryArithmetic.CanonE x :=
  FIp_DotsOutputCanonical.all _ _ _ source
#print axioms output_canonical
end AspisR1.JGw_Dots4
end
