import NDO_JFw_TX2_Raw32
import NDO_JFw_TX2_PowerReads
import NDO_JFw_TX2_CellUnique
import NDO_JFv_TX2_EbyKFinishMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1974421539#u32,1851944203#u32⟩,⟨599971432#u32,1465380718#u32⟩⟩,⟨⟨872134586#u32,5416023#u32⟩,⟨2053165608#u32,1023051361#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFw_TX2_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFw_TX2_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12711839774%2147483647 at h0
  norm_num at h0
  have e0 : a0=1974421539#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8294395144%2147483647 at h1
  norm_num at h1
  have e1 : a1=1851944203#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17779840608%2147483647 at h2
  norm_num at h2
  have e2 : a2=599971432#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10055315306%2147483647 at h3
  norm_num at h3
  have e3 : a3=1465380718#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=11609552821%2147483647 at h4
  norm_num at h4
  have e4 : a4=872134586#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6447866964%2147483647 at h5
  norm_num at h5
  have e5 : a5=5416023#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=19233034784%2147483647 at h6
  norm_num at h6
  have e6 : a6=2053165608#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9612985949%2147483647 at h7
  norm_num at h7
  have e7 : a7=1023051361#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFw_TX2_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 0))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails10.value0_3
      from JFr_TX2_Tails10.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 0))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails10.value1_3
      from JFr_TX2_Tails10.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 0))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails10.value2_3
      from JFr_TX2_Tails10.source2_3,
    JFw_TX2_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFw_TX2_Raw30.after=JFw_TX2_Raw31.before := rfl
  have same2 : JFw_TX2_Raw31.after=JFw_TX2_Raw32.before := rfl
  simp only [same1,JFw_TX2_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFw_TX2_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFw_TX2_Tail3
end
