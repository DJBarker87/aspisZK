import NDO_JFz_TX2_Q1_Raw32
import NDO_JFw_TX2_PowerReads
import NDO_JFw_TX2_CellUnique
import NDO_JFv_TX2_EbyKFinishMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1400229552#u32,1777594326#u32⟩,⟨1768698764#u32,189782373#u32⟩⟩,⟨⟨1374790651#u32,762918889#u32⟩,⟨1971777038#u32,2108732861#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q1_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q1_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12137647787%2147483647 at h0
  norm_num at h0
  have e0 : a0=1400229552#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6072561620%2147483647 at h1
  norm_num at h1
  have e1 : a1=1777594326#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18948567940%2147483647 at h2
  norm_num at h2
  have e2 : a2=1768698764#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8779716961%2147483647 at h3
  norm_num at h3
  have e3 : a3=189782373#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9964725239%2147483647 at h4
  norm_num at h4
  have e4 : a4=1374790651#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7205369830%2147483647 at h5
  norm_num at h5
  have e5 : a5=762918889#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17004162567%2147483647 at h6
  norm_num at h6
  have e6 : a6=1971777038#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10698667449%2147483647 at h7
  norm_num at h7
  have e7 : a7=2108732861#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 1)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q1_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 1))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails11.value0_3
      from JFr_TX2_Tails11.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 1))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails11.value1_3
      from JFr_TX2_Tails11.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 1))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails11.value2_3
      from JFr_TX2_Tails11.source2_3,
    JFz_TX2_Q1_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q1_Raw30.after=JFz_TX2_Q1_Raw31.before := rfl
  have same2 : JFz_TX2_Q1_Raw31.after=JFz_TX2_Q1_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q1_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q1_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q1_Tail3
end
