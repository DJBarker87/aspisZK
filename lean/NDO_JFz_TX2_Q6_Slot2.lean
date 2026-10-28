import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails16
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨179095085#u32,1937464353#u32⟩,⟨1020436422#u32,1596241460#u32⟩⟩,⟨⟨1096754262#u32,1776724220#u32⟩,⟨1666430960#u32,1924086015#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 6 2 0 0 26%2147483647=179095085 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1448177298+855639275*1187660153+867568255*1583310052+352063*841340748+1106523000*1063922525+1554033304*2140105405+1430280692*1306249690+1491718280*1156830139+118514350*1097717769+1675652887*130885513+1364884909*637937357+1135303194*803945638+304762092*228259789+1465393816*38588123+824208172*1919821933+1752653420*174707150+1385409049*1825007271+1003904973*152478396+1298953245*1534893842+2005758375*1035734995+497936241*775203422+235809508*591834492+1478307182*1537299214+1858903615*1437089951+628035096*1204184451+1244951250*1301964459)%2147483647=179095085
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 6 2 1 0 26%2147483647=1937464353 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+1483149559*1187660153+655227887*1583310052+39062738*841340748+729079828*1063922525+67370206*2140105405+1685049618*1306249690+385547620*1156830139+1786803209*1097717769+779721715*130885513+594709522*637937357+338788461*803945638+526756808*228259789+184076238*38588123+1852498770*1919821933+2102463508*174707150+1086671526*1825007271+1147694576*152478396+1504805752*1534893842+2005073905*1035734995+185008025*775203422+1485990146*591834492+1255280192*1537299214+1018329259*1437089951+570157693*1204184451+1511904630*1301964459)%2147483647=1937464353
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 6 2 2 0 26%2147483647=1020436422 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+1898717401*1187660153+1032732628*1583310052+1313565596*841340748+1074182998*1063922525+1410213748*2140105405+1182702806*1306249690+321711020*1156830139+2062791928*1097717769+1188803754*130885513+2038502201*637937357+735931834*803945638+1330533011*228259789+1052874750*38588123+950153811*1919821933+1225424092*174707150+1659116453*1825007271+1474177753*152478396+2073609211*1534893842+1602919019*1035734995+1865917845*775203422+1085624123*591834492+1837870964*1537299214+1550509101*1437089951+1661725734*1204184451+2066655336*1301964459)%2147483647=1020436422
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 6 2 3 0 26%2147483647=1596241460 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+1849775942*1187660153+656039795*1583310052+1840648083*841340748+246996287*1063922525+1369248953*2140105405+1132591724*1306249690+92744917*1156830139+1719480363*1097717769+1266677922*130885513+377386917*637937357+735227219*803945638+465096431*228259789+451889791*38588123+1379836302*1919821933+618598847*174707150+1624084534*1825007271+1511477847*152478396+1840812326*1534893842+185546252*1035734995+2145463598*775203422+82870699*591834492+1625323762*1537299214+1843639311*1437089951+1777269271*1204184451+1645120956*1301964459)%2147483647=1596241460
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 6 2 4 0 26%2147483647=1096754262 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+1112406525*1187660153+1345999435*1583310052+752376469*841340748+634588140*1063922525+1419170319*2140105405+1702860885*1306249690+710076517*1156830139+1256487405*1097717769+1114745059*130885513+1137838899*637937357+1254184109*803945638+1038210451*228259789+274378589*38588123+171986381*1919821933+1536678585*174707150+1305878831*1825007271+1335902916*152478396+1755193245*1534893842+2023391453*1035734995+293456010*775203422+1751078325*591834492+1423042536*1537299214+1749638204*1437089951+1345811362*1204184451+1284924881*1301964459)%2147483647=1096754262
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 6 2 5 0 26%2147483647=1776724220 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+1796814865*1187660153+1253123171*1583310052+1317611639*841340748+1559245386*1063922525+1866942376*2140105405+1973593402*1306249690+47019780*1156830139+1353487525*1097717769+1840161555*130885513+2003659556*637937357+200559114*803945638+334988447*228259789+2023650872*38588123+1296497964*1919821933+34285357*174707150+1685894190*1825007271+995962325*152478396+1295624230*1534893842+1199631211*1035734995+1948677857*775203422+1425322328*591834492+1466877680*1537299214+702011012*1437089951+937706871*1204184451+455802666*1301964459)%2147483647=1776724220
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 6 2 6 0 26%2147483647=1666430960 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+1838939499*1187660153+1353876630*1583310052+1258713036*841340748+1947503436*1063922525+1271796599*2140105405+1660157177*1306249690+564707688*1156830139+1858113864*1097717769+1015817431*130885513+1264608004*637937357+735383960*803945638+221696734*228259789+1297524163*38588123+109088572*1919821933+792206628*174707150+1921581249*1825007271+94118806*152478396+476103426*1534893842+239612482*1035734995+177052717*775203422+826458039*591834492+1923715623*1537299214+1014161165*1437089951+1341609618*1204184451+786325583*1301964459)%2147483647=1666430960
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 6 2 7 0 26%2147483647=1924086015 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1448177298+418714188*1187660153+1675147475*1583310052+1674326661*841340748+547797802*1063922525+2073962627*2140105405+897270857*1306249690+1582958967*1156830139+49892701*1097717769+1256824732*130885513+1435903714*637937357+742583315*803945638+1789294768*228259789+13407412*38588123+518661610*1919821933+1259751297*174707150+1695663205*1825007271+2068940067*152478396+940478841*1534893842+1982757556*1035734995+1956713516*775203422+863066484*591834492+522298462*1537299214+1343575777*1437089951+771712139*1204184451+157728743*1301964459)%2147483647=1924086015
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 6 2
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
end AspisR1.JFz_TX2_Q6_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4669914872#u64 2635267009#u64 5859250702#u64 3834609759#u64⟩,⟨pack 3990403612#u64 943024915#u64 5513423642#u64 2071845460#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 6262570343085834721#u64 1324860611683502168#u64 11091281414403180209#u64 3965701088450805790#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 816368640#u32 64212650#u32 1161785526#u32 914200205#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 816368640#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 64212650#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1161785526#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 914200205#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4896865253669627931#u64 1044620591127523658#u64 10147182100289952355#u64 3689648660935955075#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 816368640#u32 64212650#u32 1161785526#u32 914200205#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 816368640#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 64212650#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1161785526#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 816368640#u32) (JFs_TX2_RawMath.extend 64212650#u32) (JFs_TX2_RawMath.extend 1161785526#u32) (JFs_TX2_RawMath.extend 914200205#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 914200205#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails16.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value0_2=
      ok (.Ok (pack 816368640#u32 64212650#u32 1161785526#u32 914200205#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (816368640<2147483647 ∧ 64212650<2147483647) ∧ (1161785526<2147483647 ∧ 914200205<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 816368640#u32 64212650#u32 1161785526#u32 914200205#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 816368640#u32 64212650#u32 1161785526#u32 914200205#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q6_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4669914872#u64 2635267009#u64 5859250702#u64 3834609759#u64⟩,⟨pack 3990403612#u64 943024915#u64 5513423642#u64 2071845460#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8366728176#u64 5071452613#u64 10100434433#u64 8205195647#u64⟩,⟨pack 7805706893#u64 3187578036#u64 9840561674#u64 4413431781#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4229898072893794611#u64 3634609604615457193#u64 8656425071113910905#u64 5032626024149607352#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 160128333#u32 1876030754#u32 1029333279#u32 854028436#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 160128333#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1876030754#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1029333279#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 854028436#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4265231398845455802#u64 1248003616823152711#u64 8685291501285682619#u64 1751469563695125758#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 160128333#u32 1876030754#u32 1029333279#u32 854028436#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 160128333#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1876030754#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1029333279#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 160128333#u32) (JFs_TX2_RawMath.extend 1876030754#u32) (JFs_TX2_RawMath.extend 1029333279#u32) (JFs_TX2_RawMath.extend 854028436#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 854028436#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails16.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value1_2=
      ok (.Ok (pack 160128333#u32 1876030754#u32 1029333279#u32 854028436#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (160128333<2147483647 ∧ 1876030754<2147483647) ∧ (1029333279<2147483647 ∧ 854028436<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 160128333#u32 1876030754#u32 1029333279#u32 854028436#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4669914872#u64 2635267009#u64 5859250702#u64 3834609759#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 160128333#u32 1876030754#u32 1029333279#u32 854028436#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3990403612#u64 943024915#u64 5513423642#u64 2071845460#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8366728176#u64 5071452613#u64 10100434433#u64 8205195647#u64⟩,⟨pack 7805706893#u64 3187578036#u64 9840561674#u64 4413431781#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11314536207#u64 5762431865#u64 15847049172#u64 11354971894#u64⟩,⟨pack 12512729793#u64 5033897782#u64 17510500984#u64 10383461965#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5272960897019107104#u64 832289854675336007#u64 10260058112354437335#u64 2949129161599546054#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1397975155#u32 90699820#u32 1732129253#u32 1669413508#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1397975155#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 90699820#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1732129253#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1669413508#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 6925492789695668789#u64 2744401924955599997#u64 12020406468244659313#u64 8914444337529126559#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1397975155#u32 90699820#u32 1732129253#u32 1669413508#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1397975155#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 90699820#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1732129253#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1397975155#u32) (JFs_TX2_RawMath.extend 90699820#u32) (JFs_TX2_RawMath.extend 1732129253#u32) (JFs_TX2_RawMath.extend 1669413508#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1669413508#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails16.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value2_2=
      ok (.Ok (pack 1397975155#u32 90699820#u32 1732129253#u32 1669413508#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1397975155<2147483647 ∧ 90699820<2147483647) ∧ (1732129253<2147483647 ∧ 1669413508<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1397975155#u32 90699820#u32 1732129253#u32 1669413508#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8366728176#u64 5071452613#u64 10100434433#u64 8205195647#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1397975155#u32 90699820#u32 1732129253#u32 1669413508#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7805706893#u64 3187578036#u64 9840561674#u64 4413431781#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨577117972#u32,1467464571#u32⟩,⟨814663643#u32,617553659#u32⟩⟩,⟨⟨1775311558#u32,738930488#u32⟩,⟨330631808#u32,1793527377#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q6_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q6_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11314536207%2147483647 at h0
  norm_num at h0
  have e0 : a0=577117972#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5762431865%2147483647 at h1
  norm_num at h1
  have e1 : a1=1467464571#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15847049172%2147483647 at h2
  norm_num at h2
  have e2 : a2=814663643#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11354971894%2147483647 at h3
  norm_num at h3
  have e3 : a3=617553659#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=12512729793%2147483647 at h4
  norm_num at h4
  have e4 : a4=1775311558#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5033897782%2147483647 at h5
  norm_num at h5
  have e5 : a5=738930488#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17510500984%2147483647 at h6
  norm_num at h6
  have e6 : a6=330631808#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10383461965%2147483647 at h7
  norm_num at h7
  have e7 : a7=1793527377#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q6_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails16.value0_2
      from JFr_TX2_Tails16.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails16.value1_2
      from JFr_TX2_Tails16.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails16.value2_2
      from JFr_TX2_Tails16.source2_2,
    JFz_TX2_Q6_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q6_Raw20.after=JFz_TX2_Q6_Raw21.before := rfl
  have same2 : JFz_TX2_Q6_Raw21.after=JFz_TX2_Q6_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q6_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q6_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q6_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨756213057#u32,1257445277#u32⟩,⟨1835100065#u32,66311472#u32⟩⟩,⟨⟨724582173#u32,368171061#u32⟩,⟨1997062768#u32,1570129745#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((756213057<2147483647 ∧ 1257445277<2147483647) ∧ (1835100065<2147483647 ∧ 66311472<2147483647)) ∧
    ((724582173<2147483647 ∧ 368171061<2147483647) ∧ (1997062768<2147483647 ∧ 1570129745<2147483647))
  omega
theorem addition : decode JFz_TX2_Q6_Head2.value+decode JFz_TX2_Q6_Tail2.value=decode value := by
  change (⟨⟨⟨179095085,1937464353⟩,⟨1020436422,1596241460⟩⟩,⟨⟨1096754262,1776724220⟩,⟨1666430960,1924086015⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨577117972,1467464571⟩,⟨814663643,617553659⟩⟩,⟨⟨1775311558,738930488⟩,⟨330631808,1793527377⟩⟩⟩=⟨⟨⟨756213057,1257445277⟩,⟨1835100065,66311472⟩⟩,⟨⟨724582173,368171061⟩,⟨1997062768,1570129745⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 6 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q6_Head2.value JFz_TX2_Q6_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q6_Head2.source,
      JFz_TX2_Q6_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q6_Head2.value := by
    change ((179095085<2147483647 ∧ 1937464353<2147483647) ∧ (1020436422<2147483647 ∧ 1596241460<2147483647)) ∧
      ((1096754262<2147483647 ∧ 1776724220<2147483647) ∧ (1666430960<2147483647 ∧ 1924086015<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q6_Tail2.value := by
    change ((577117972<2147483647 ∧ 1467464571<2147483647) ∧ (814663643<2147483647 ∧ 617553659<2147483647)) ∧
      ((1775311558<2147483647 ∧ 738930488<2147483647) ∧ (330631808<2147483647 ∧ 1793527377<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q6_Dot2
end
