import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails13
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1283058323#u32,1601476955#u32⟩,⟨1046366244#u32,315758845#u32⟩⟩,⟨⟨258824856#u32,1972696497#u32⟩,⟨95422151#u32,1872861736#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 3 2 0 0 26%2147483647=1283058323 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1823140230+855639275*2100023176+867568255*246113585+352063*2100405010+1106523000*1964007974+1554033304*802616952+1430280692*501579321+1491718280*1464913590+118514350*1551879726+1675652887*211362866+1364884909*1989256385+1135303194*409200794+304762092*657822582+1465393816*421595677+824208172*273129674+1752653420*1063289601+1385409049*2041298464+1003904973*881676161+1298953245*527707106+2005758375*681014773+497936241*235242336+235809508*1649176012+1478307182*2026804618+1858903615*1294442356+628035096*1361358964+1244951250*467616324)%2147483647=1283058323
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 3 2 1 0 26%2147483647=1601476955 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+1483149559*2100023176+655227887*246113585+39062738*2100405010+729079828*1964007974+67370206*802616952+1685049618*501579321+385547620*1464913590+1786803209*1551879726+779721715*211362866+594709522*1989256385+338788461*409200794+526756808*657822582+184076238*421595677+1852498770*273129674+2102463508*1063289601+1086671526*2041298464+1147694576*881676161+1504805752*527707106+2005073905*681014773+185008025*235242336+1485990146*1649176012+1255280192*2026804618+1018329259*1294442356+570157693*1361358964+1511904630*467616324)%2147483647=1601476955
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 3 2 2 0 26%2147483647=1046366244 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+1898717401*2100023176+1032732628*246113585+1313565596*2100405010+1074182998*1964007974+1410213748*802616952+1182702806*501579321+321711020*1464913590+2062791928*1551879726+1188803754*211362866+2038502201*1989256385+735931834*409200794+1330533011*657822582+1052874750*421595677+950153811*273129674+1225424092*1063289601+1659116453*2041298464+1474177753*881676161+2073609211*527707106+1602919019*681014773+1865917845*235242336+1085624123*1649176012+1837870964*2026804618+1550509101*1294442356+1661725734*1361358964+2066655336*467616324)%2147483647=1046366244
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 3 2 3 0 26%2147483647=315758845 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+1849775942*2100023176+656039795*246113585+1840648083*2100405010+246996287*1964007974+1369248953*802616952+1132591724*501579321+92744917*1464913590+1719480363*1551879726+1266677922*211362866+377386917*1989256385+735227219*409200794+465096431*657822582+451889791*421595677+1379836302*273129674+618598847*1063289601+1624084534*2041298464+1511477847*881676161+1840812326*527707106+185546252*681014773+2145463598*235242336+82870699*1649176012+1625323762*2026804618+1843639311*1294442356+1777269271*1361358964+1645120956*467616324)%2147483647=315758845
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 3 2 4 0 26%2147483647=258824856 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+1112406525*2100023176+1345999435*246113585+752376469*2100405010+634588140*1964007974+1419170319*802616952+1702860885*501579321+710076517*1464913590+1256487405*1551879726+1114745059*211362866+1137838899*1989256385+1254184109*409200794+1038210451*657822582+274378589*421595677+171986381*273129674+1536678585*1063289601+1305878831*2041298464+1335902916*881676161+1755193245*527707106+2023391453*681014773+293456010*235242336+1751078325*1649176012+1423042536*2026804618+1749638204*1294442356+1345811362*1361358964+1284924881*467616324)%2147483647=258824856
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 3 2 5 0 26%2147483647=1972696497 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+1796814865*2100023176+1253123171*246113585+1317611639*2100405010+1559245386*1964007974+1866942376*802616952+1973593402*501579321+47019780*1464913590+1353487525*1551879726+1840161555*211362866+2003659556*1989256385+200559114*409200794+334988447*657822582+2023650872*421595677+1296497964*273129674+34285357*1063289601+1685894190*2041298464+995962325*881676161+1295624230*527707106+1199631211*681014773+1948677857*235242336+1425322328*1649176012+1466877680*2026804618+702011012*1294442356+937706871*1361358964+455802666*467616324)%2147483647=1972696497
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 3 2 6 0 26%2147483647=95422151 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+1838939499*2100023176+1353876630*246113585+1258713036*2100405010+1947503436*1964007974+1271796599*802616952+1660157177*501579321+564707688*1464913590+1858113864*1551879726+1015817431*211362866+1264608004*1989256385+735383960*409200794+221696734*657822582+1297524163*421595677+109088572*273129674+792206628*1063289601+1921581249*2041298464+94118806*881676161+476103426*527707106+239612482*681014773+177052717*235242336+826458039*1649176012+1923715623*2026804618+1014161165*1294442356+1341609618*1361358964+786325583*467616324)%2147483647=95422151
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 3 2 7 0 26%2147483647=1872861736 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1823140230+418714188*2100023176+1675147475*246113585+1674326661*2100405010+547797802*1964007974+2073962627*802616952+897270857*501579321+1582958967*1464913590+49892701*1551879726+1256824732*211362866+1435903714*1989256385+742583315*409200794+1789294768*657822582+13407412*421595677+518661610*273129674+1259751297*1063289601+1695663205*2041298464+2068940067*881676161+940478841*527707106+1982757556*681014773+1956713516*235242336+863066484*1649176012+522298462*2026804618+1343575777*1294442356+771712139*1361358964+157728743*467616324)%2147483647=1872861736
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 3 2
  have same : out=value := JFw_TX2_CellUnique.source out value (by
    intro j
    fin_cases j
    · exact (h 0).trans lane0
    · exact (h 1).trans lane1
    · exact (h 2).trans lane2
    · exact (h 3).trans lane3
    · exact (h 4).trans lane4
    · exact (h 5).trans lane5
    · exact (h 6).trans lane6
    · exact (h 7).trans lane7
    )
  exact same ▸ run
#print axioms lane0
#print axioms lane1
#print axioms lane2
#print axioms lane3
#print axioms lane4
#print axioms lane5
#print axioms lane6
#print axioms lane7
#print axioms source
end AspisR1.JFz_TX2_Q3_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2388683288#u64 2309136803#u64 4787851101#u64 5189019417#u64⟩,⟨pack 3151293628#u64 1782697384#u64 4572326091#u64 5103209361#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4204530334742441464#u64 4373292138801169812#u64 8590964691301193120#u64 7214425575883838317#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 821989062#u32 1487113936#u32 935427493#u32 1987274250#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 821989062#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1487113936#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 935427493#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1987274250#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3128694185020765995#u64 1687947666872874685#u64 5753441310037475333#u64 6820557872139456787#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 821989062#u32 1487113936#u32 935427493#u32 1987274250#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 821989062#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1487113936#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 935427493#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 821989062#u32) (JFs_TX2_RawMath.extend 1487113936#u32) (JFs_TX2_RawMath.extend 935427493#u32) (JFs_TX2_RawMath.extend 1987274250#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1987274250#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails13.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value0_2=
      ok (.Ok (pack 821989062#u32 1487113936#u32 935427493#u32 1987274250#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (821989062<2147483647 ∧ 1487113936<2147483647) ∧ (935427493<2147483647 ∧ 1987274250<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 821989062#u32 1487113936#u32 935427493#u32 1987274250#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 821989062#u32 1487113936#u32 935427493#u32 1987274250#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw1=_
    simp only [raw1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add before.count 1#usize=after.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment before.count (by unfold before;decide)
  rw [inc]
#print axioms pair0
#print axioms pair1
#print axioms source
end AspisR1.JFz_TX2_Q3_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2388683288#u64 2309136803#u64 4787851101#u64 5189019417#u64⟩,⟨pack 3151293628#u64 1782697384#u64 4572326091#u64 5103209361#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7521610861#u64 5707017490#u64 9997502689#u64 10816676078#u64⟩,⟨pack 5969171514#u64 3962514118#u64 9862467317#u64 7711115896#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6595357829113277525#u64 4027778414977774894#u64 9436298404328901302#u64 8427776305998874122#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1395142704#u32 1845024958#u32 642076904#u32 1885545046#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1395142704#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1845024958#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 642076904#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1885545046#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5068971259904406140#u64 1524055924398902155#u64 8773945208506844366#u64 3014325622119296138#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1395142704#u32 1845024958#u32 642076904#u32 1885545046#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1395142704#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1845024958#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 642076904#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395142704#u32) (JFs_TX2_RawMath.extend 1845024958#u32) (JFs_TX2_RawMath.extend 642076904#u32) (JFs_TX2_RawMath.extend 1885545046#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1885545046#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails13.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value1_2=
      ok (.Ok (pack 1395142704#u32 1845024958#u32 642076904#u32 1885545046#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1395142704<2147483647 ∧ 1845024958<2147483647) ∧ (642076904<2147483647 ∧ 1885545046<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1395142704#u32 1845024958#u32 642076904#u32 1885545046#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2388683288#u64 2309136803#u64 4787851101#u64 5189019417#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1395142704#u32 1845024958#u32 642076904#u32 1885545046#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3151293628#u64 1782697384#u64 4572326091#u64 5103209361#u64⟩ raw1=_
    simp only [raw1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add before.count 1#usize=after.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment before.count (by unfold before;decide)
  rw [inc]
#print axioms pair0
#print axioms pair1
#print axioms source
end AspisR1.JFz_TX2_Q3_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7521610861#u64 5707017490#u64 9997502689#u64 10816676078#u64⟩,⟨pack 5969171514#u64 3962514118#u64 9862467317#u64 7711115896#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10702820323#u64 7253100022#u64 15784185539#u64 13303521138#u64⟩,⟨pack 10124325661#u64 7764272479#u64 17825725244#u64 12241822839#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5188724616395836510#u64 1223361492530943821#u64 10460083855344166961#u64 2636651890658227371#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1705352526#u32 519025716#u32 1089890831#u32 613969994#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1705352526#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 519025716#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1089890831#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 613969994#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 6679558810803470385#u64 4072706339519850733#u64 12701068478654654286#u64 7327522502994553910#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1705352526#u32 519025716#u32 1089890831#u32 613969994#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1705352526#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 519025716#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1089890831#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1705352526#u32) (JFs_TX2_RawMath.extend 519025716#u32) (JFs_TX2_RawMath.extend 1089890831#u32) (JFs_TX2_RawMath.extend 613969994#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 613969994#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails13.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value2_2=
      ok (.Ok (pack 1705352526#u32 519025716#u32 1089890831#u32 613969994#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1705352526<2147483647 ∧ 519025716<2147483647) ∧ (1089890831<2147483647 ∧ 613969994<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1705352526#u32 519025716#u32 1089890831#u32 613969994#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7521610861#u64 5707017490#u64 9997502689#u64 10816676078#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1705352526#u32 519025716#u32 1089890831#u32 613969994#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5969171514#u64 3962514118#u64 9862467317#u64 7711115896#u64⟩ raw1=_
    simp only [raw1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add before.count 1#usize=after.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment before.count (by unfold before;decide)
  rw [inc]
#print axioms pair0
#print axioms pair1
#print axioms source
end AspisR1.JFz_TX2_Q3_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨2112885735#u32,810649081#u32⟩,⟨751800010#u32,418619256#u32⟩⟩,⟨⟨1534391073#u32,1321821538#u32⟩,⟨645856068#u32,1504404604#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q3_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q3_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10702820323%2147483647 at h0
  norm_num at h0
  have e0 : a0=2112885735#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7253100022%2147483647 at h1
  norm_num at h1
  have e1 : a1=810649081#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15784185539%2147483647 at h2
  norm_num at h2
  have e2 : a2=751800010#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=13303521138%2147483647 at h3
  norm_num at h3
  have e3 : a3=418619256#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10124325661%2147483647 at h4
  norm_num at h4
  have e4 : a4=1534391073#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7764272479%2147483647 at h5
  norm_num at h5
  have e5 : a5=1321821538#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17825725244%2147483647 at h6
  norm_num at h6
  have e6 : a6=645856068#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12241822839%2147483647 at h7
  norm_num at h7
  have e7 : a7=1504404604#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q3_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails13.value0_2
      from JFr_TX2_Tails13.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails13.value1_2
      from JFr_TX2_Tails13.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails13.value2_2
      from JFr_TX2_Tails13.source2_2,
    JFz_TX2_Q3_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q3_Raw20.after=JFz_TX2_Q3_Raw21.before := rfl
  have same2 : JFz_TX2_Q3_Raw21.after=JFz_TX2_Q3_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q3_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q3_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q3_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1248460411#u32,264642389#u32⟩,⟨1798166254#u32,734378101#u32⟩⟩,⟨⟨1793215929#u32,1147034388#u32⟩,⟨741278219#u32,1229782693#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1248460411<2147483647 ∧ 264642389<2147483647) ∧ (1798166254<2147483647 ∧ 734378101<2147483647)) ∧
    ((1793215929<2147483647 ∧ 1147034388<2147483647) ∧ (741278219<2147483647 ∧ 1229782693<2147483647))
  omega
theorem addition : decode JFz_TX2_Q3_Head2.value+decode JFz_TX2_Q3_Tail2.value=decode value := by
  change (⟨⟨⟨1283058323,1601476955⟩,⟨1046366244,315758845⟩⟩,⟨⟨258824856,1972696497⟩,⟨95422151,1872861736⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨2112885735,810649081⟩,⟨751800010,418619256⟩⟩,⟨⟨1534391073,1321821538⟩,⟨645856068,1504404604⟩⟩⟩=⟨⟨⟨1248460411,264642389⟩,⟨1798166254,734378101⟩⟩,⟨⟨1793215929,1147034388⟩,⟨741278219,1229782693⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 3 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q3_Head2.value JFz_TX2_Q3_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q3_Head2.source,
      JFz_TX2_Q3_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q3_Head2.value := by
    change ((1283058323<2147483647 ∧ 1601476955<2147483647) ∧ (1046366244<2147483647 ∧ 315758845<2147483647)) ∧
      ((258824856<2147483647 ∧ 1972696497<2147483647) ∧ (95422151<2147483647 ∧ 1872861736<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q3_Tail2.value := by
    change ((2112885735<2147483647 ∧ 810649081<2147483647) ∧ (751800010<2147483647 ∧ 418619256<2147483647)) ∧
      ((1534391073<2147483647 ∧ 1321821538<2147483647) ∧ (645856068<2147483647 ∧ 1504404604<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q3_Dot2
end
