import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails18
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨765082999#u32,590702472#u32⟩,⟨2042627496#u32,21967208#u32⟩⟩,⟨⟨485974454#u32,1210198081#u32⟩,⟨1230680209#u32,795213070#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 8 1 0 0 26%2147483647=765082999 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*192119377+855639275*761251415+867568255*1030327953+352063*1269243596+1106523000*1899232601+1554033304*543977519+1430280692*1647663637+1491718280*281586361+118514350*905151138+1675652887*1715231337+1364884909*2112999760+1135303194*1370074022+304762092*1686086215+1465393816*1297068139+824208172*248692339+1752653420*539464940+1385409049*1710573392+1003904973*140019460+1298953245*94842679+2005758375*708472459+497936241*1355621429+235809508*1385267213+1478307182*2127504144+1858903615*1428630765+628035096*2069777778+1244951250*205496523)%2147483647=765082999
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 8 1 1 0 26%2147483647=590702472 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+1483149559*761251415+655227887*1030327953+39062738*1269243596+729079828*1899232601+67370206*543977519+1685049618*1647663637+385547620*281586361+1786803209*905151138+779721715*1715231337+594709522*2112999760+338788461*1370074022+526756808*1686086215+184076238*1297068139+1852498770*248692339+2102463508*539464940+1086671526*1710573392+1147694576*140019460+1504805752*94842679+2005073905*708472459+185008025*1355621429+1485990146*1385267213+1255280192*2127504144+1018329259*1428630765+570157693*2069777778+1511904630*205496523)%2147483647=590702472
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 8 1 2 0 26%2147483647=2042627496 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+1898717401*761251415+1032732628*1030327953+1313565596*1269243596+1074182998*1899232601+1410213748*543977519+1182702806*1647663637+321711020*281586361+2062791928*905151138+1188803754*1715231337+2038502201*2112999760+735931834*1370074022+1330533011*1686086215+1052874750*1297068139+950153811*248692339+1225424092*539464940+1659116453*1710573392+1474177753*140019460+2073609211*94842679+1602919019*708472459+1865917845*1355621429+1085624123*1385267213+1837870964*2127504144+1550509101*1428630765+1661725734*2069777778+2066655336*205496523)%2147483647=2042627496
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 8 1 3 0 26%2147483647=21967208 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+1849775942*761251415+656039795*1030327953+1840648083*1269243596+246996287*1899232601+1369248953*543977519+1132591724*1647663637+92744917*281586361+1719480363*905151138+1266677922*1715231337+377386917*2112999760+735227219*1370074022+465096431*1686086215+451889791*1297068139+1379836302*248692339+618598847*539464940+1624084534*1710573392+1511477847*140019460+1840812326*94842679+185546252*708472459+2145463598*1355621429+82870699*1385267213+1625323762*2127504144+1843639311*1428630765+1777269271*2069777778+1645120956*205496523)%2147483647=21967208
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 8 1 4 0 26%2147483647=485974454 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+1112406525*761251415+1345999435*1030327953+752376469*1269243596+634588140*1899232601+1419170319*543977519+1702860885*1647663637+710076517*281586361+1256487405*905151138+1114745059*1715231337+1137838899*2112999760+1254184109*1370074022+1038210451*1686086215+274378589*1297068139+171986381*248692339+1536678585*539464940+1305878831*1710573392+1335902916*140019460+1755193245*94842679+2023391453*708472459+293456010*1355621429+1751078325*1385267213+1423042536*2127504144+1749638204*1428630765+1345811362*2069777778+1284924881*205496523)%2147483647=485974454
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 8 1 5 0 26%2147483647=1210198081 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+1796814865*761251415+1253123171*1030327953+1317611639*1269243596+1559245386*1899232601+1866942376*543977519+1973593402*1647663637+47019780*281586361+1353487525*905151138+1840161555*1715231337+2003659556*2112999760+200559114*1370074022+334988447*1686086215+2023650872*1297068139+1296497964*248692339+34285357*539464940+1685894190*1710573392+995962325*140019460+1295624230*94842679+1199631211*708472459+1948677857*1355621429+1425322328*1385267213+1466877680*2127504144+702011012*1428630765+937706871*2069777778+455802666*205496523)%2147483647=1210198081
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 8 1 6 0 26%2147483647=1230680209 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+1838939499*761251415+1353876630*1030327953+1258713036*1269243596+1947503436*1899232601+1271796599*543977519+1660157177*1647663637+564707688*281586361+1858113864*905151138+1015817431*1715231337+1264608004*2112999760+735383960*1370074022+221696734*1686086215+1297524163*1297068139+109088572*248692339+792206628*539464940+1921581249*1710573392+94118806*140019460+476103426*94842679+239612482*708472459+177052717*1355621429+826458039*1385267213+1923715623*2127504144+1014161165*1428630765+1341609618*2069777778+786325583*205496523)%2147483647=1230680209
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 8 1 7 0 26%2147483647=795213070 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*192119377+418714188*761251415+1675147475*1030327953+1674326661*1269243596+547797802*1899232601+2073962627*543977519+897270857*1647663637+1582958967*281586361+49892701*905151138+1256824732*1715231337+1435903714*2112999760+742583315*1370074022+1789294768*1686086215+13407412*1297068139+518661610*248692339+1259751297*539464940+1695663205*1710573392+2068940067*140019460+940478841*94842679+1982757556*708472459+1956713516*1355621429+863066484*1385267213+522298462*2127504144+1343575777*1428630765+771712139*2069777778+157728743*205496523)%2147483647=795213070
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 8 1
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
end AspisR1.JFz_TX2_Q8_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2070811791#u64 4368052435#u64 5377605834#u64 4659111346#u64⟩,⟨pack 2331714909#u64 2356913124#u64 3586647307#u64 4284069843#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4295993514081203681#u64 5394580677702214589#u64 7600374096627751129#u64 6940113609935809685#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1073599408#u32 1793781330#u32 440152055#u32 2028535985#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1073599408#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1793781330#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 440152055#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2028535985#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2859593807259533960#u64 2138200343838904352#u64 5357296299917312984#u64 7377169618837161590#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1073599408#u32 1793781330#u32 440152055#u32 2028535985#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1073599408#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1793781330#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 440152055#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1073599408#u32) (JFs_TX2_RawMath.extend 1793781330#u32) (JFs_TX2_RawMath.extend 440152055#u32) (JFs_TX2_RawMath.extend 2028535985#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2028535985#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails18.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value0_1=
      ok (.Ok (pack 1073599408#u32 1793781330#u32 440152055#u32 2028535985#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1073599408<2147483647 ∧ 1793781330<2147483647) ∧ (440152055<2147483647 ∧ 2028535985<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1073599408#u32 1793781330#u32 440152055#u32 2028535985#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1073599408#u32 1793781330#u32 440152055#u32 2028535985#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q8_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2070811791#u64 4368052435#u64 5377605834#u64 4659111346#u64⟩,⟨pack 2331714909#u64 2356913124#u64 3586647307#u64 4284069843#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5358565954#u64 6273980473#u64 11637714126#u64 6022093012#u64⟩,⟨pack 6508765281#u64 4408896730#u64 9081080907#u64 5662489142#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4498512018610539522#u64 1977757716951947026#u64 10082106459552481076#u64 2848045420921282225#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 134982767#u32 1011641486#u32 1114111247#u32 390130645#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 134982767#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1011641486#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1114111247#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 390130645#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4456220060671369715#u64 684638634339345035#u64 9332914788045688358#u64 1060845118278811740#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 134982767#u32 1011641486#u32 1114111247#u32 390130645#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 134982767#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1011641486#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1114111247#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 134982767#u32) (JFs_TX2_RawMath.extend 1011641486#u32) (JFs_TX2_RawMath.extend 1114111247#u32) (JFs_TX2_RawMath.extend 390130645#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 390130645#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails18.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value1_1=
      ok (.Ok (pack 134982767#u32 1011641486#u32 1114111247#u32 390130645#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (134982767<2147483647 ∧ 1011641486<2147483647) ∧ (1114111247<2147483647 ∧ 390130645<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 134982767#u32 1011641486#u32 1114111247#u32 390130645#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2070811791#u64 4368052435#u64 5377605834#u64 4659111346#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 134982767#u32 1011641486#u32 1114111247#u32 390130645#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2331714909#u64 2356913124#u64 3586647307#u64 4284069843#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5358565954#u64 6273980473#u64 11637714126#u64 6022093012#u64⟩,⟨pack 6508765281#u64 4408896730#u64 9081080907#u64 5662489142#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9365714153#u64 7247980434#u64 16940023761#u64 8245521364#u64⟩,⟨pack 8623533112#u64 8155115774#u64 14095702227#u64 11488664112#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4314550364592898371#u64 1955293413574761817#u64 9541907449703005817#u64 4125021728231966768#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1646592288#u32 2020429721#u32 1596719592#u32 615250054#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1646592288#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2020429721#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1596719592#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 615250054#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3800717019860374491#u64 6629123350910993155#u64 10726745707998015425#u64 11352322839235347719#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1646592288#u32 2020429721#u32 1596719592#u32 615250054#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1646592288#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2020429721#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1596719592#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1646592288#u32) (JFs_TX2_RawMath.extend 2020429721#u32) (JFs_TX2_RawMath.extend 1596719592#u32) (JFs_TX2_RawMath.extend 615250054#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 615250054#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails18.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value2_1=
      ok (.Ok (pack 1646592288#u32 2020429721#u32 1596719592#u32 615250054#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1646592288<2147483647 ∧ 2020429721<2147483647) ∧ (1596719592<2147483647 ∧ 615250054<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1646592288#u32 2020429721#u32 1596719592#u32 615250054#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5358565954#u64 6273980473#u64 11637714126#u64 6022093012#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1646592288#u32 2020429721#u32 1596719592#u32 615250054#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6508765281#u64 4408896730#u64 9081080907#u64 5662489142#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨775779565#u32,805529493#u32⟩,⟨1907638232#u32,1803070423#u32⟩⟩,⟨⟨33598524#u32,1712664833#u32⟩,⟨1210800345#u32,751245877#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q8_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q8_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9365714153%2147483647 at h0
  norm_num at h0
  have e0 : a0=775779565#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7247980434%2147483647 at h1
  norm_num at h1
  have e1 : a1=805529493#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16940023761%2147483647 at h2
  norm_num at h2
  have e2 : a2=1907638232#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8245521364%2147483647 at h3
  norm_num at h3
  have e3 : a3=1803070423#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8623533112%2147483647 at h4
  norm_num at h4
  have e4 : a4=33598524#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=8155115774%2147483647 at h5
  norm_num at h5
  have e5 : a5=1712664833#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14095702227%2147483647 at h6
  norm_num at h6
  have e6 : a6=1210800345#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11488664112%2147483647 at h7
  norm_num at h7
  have e7 : a7=751245877#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q8_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails18.value0_1
      from JFr_TX2_Tails18.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails18.value1_1
      from JFr_TX2_Tails18.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails18.value2_1
      from JFr_TX2_Tails18.source2_1,
    JFz_TX2_Q8_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q8_Raw10.after=JFz_TX2_Q8_Raw11.before := rfl
  have same2 : JFz_TX2_Q8_Raw11.after=JFz_TX2_Q8_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q8_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q8_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q8_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1540862564#u32,1396231965#u32⟩,⟨1802782081#u32,1825037631#u32⟩⟩,⟨⟨519572978#u32,775379267#u32⟩,⟨293996907#u32,1546458947#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1540862564<2147483647 ∧ 1396231965<2147483647) ∧ (1802782081<2147483647 ∧ 1825037631<2147483647)) ∧
    ((519572978<2147483647 ∧ 775379267<2147483647) ∧ (293996907<2147483647 ∧ 1546458947<2147483647))
  omega
theorem addition : decode JFz_TX2_Q8_Head1.value+decode JFz_TX2_Q8_Tail1.value=decode value := by
  change (⟨⟨⟨765082999,590702472⟩,⟨2042627496,21967208⟩⟩,⟨⟨485974454,1210198081⟩,⟨1230680209,795213070⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨775779565,805529493⟩,⟨1907638232,1803070423⟩⟩,⟨⟨33598524,1712664833⟩,⟨1210800345,751245877⟩⟩⟩=⟨⟨⟨1540862564,1396231965⟩,⟨1802782081,1825037631⟩⟩,⟨⟨519572978,775379267⟩,⟨293996907,1546458947⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 8 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q8_Head1.value JFz_TX2_Q8_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q8_Head1.source,
      JFz_TX2_Q8_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q8_Head1.value := by
    change ((765082999<2147483647 ∧ 590702472<2147483647) ∧ (2042627496<2147483647 ∧ 21967208<2147483647)) ∧
      ((485974454<2147483647 ∧ 1210198081<2147483647) ∧ (1230680209<2147483647 ∧ 795213070<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q8_Tail1.value := by
    change ((775779565<2147483647 ∧ 805529493<2147483647) ∧ (1907638232<2147483647 ∧ 1803070423<2147483647)) ∧
      ((33598524<2147483647 ∧ 1712664833<2147483647) ∧ (1210800345<2147483647 ∧ 751245877<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q8_Dot1
end
