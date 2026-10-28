import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails20
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1656230473#u32,1054306584#u32⟩,⟨980358637#u32,627064808#u32⟩⟩,⟨⟨1897903933#u32,229148989#u32⟩,⟨76084977#u32,749296556#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 10 1 0 0 26%2147483647=1656230473 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*2077540809+855639275*1887634218+867568255*332708175+352063*1980751118+1106523000*608201127+1554033304*659828919+1430280692*1247578007+1491718280*1522110668+118514350*335850616+1675652887*1578178749+1364884909*331194581+1135303194*384407195+304762092*259537024+1465393816*1634746634+824208172*74403794+1752653420*2001962511+1385409049*465233830+1003904973*480792153+1298953245*323007149+2005758375*2046808035+497936241*177661286+235809508*748181341+1478307182*1444239702+1858903615*2026249346+628035096*2146621927+1244951250*927536095)%2147483647=1656230473
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 10 1 1 0 26%2147483647=1054306584 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+1483149559*1887634218+655227887*332708175+39062738*1980751118+729079828*608201127+67370206*659828919+1685049618*1247578007+385547620*1522110668+1786803209*335850616+779721715*1578178749+594709522*331194581+338788461*384407195+526756808*259537024+184076238*1634746634+1852498770*74403794+2102463508*2001962511+1086671526*465233830+1147694576*480792153+1504805752*323007149+2005073905*2046808035+185008025*177661286+1485990146*748181341+1255280192*1444239702+1018329259*2026249346+570157693*2146621927+1511904630*927536095)%2147483647=1054306584
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 10 1 2 0 26%2147483647=980358637 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+1898717401*1887634218+1032732628*332708175+1313565596*1980751118+1074182998*608201127+1410213748*659828919+1182702806*1247578007+321711020*1522110668+2062791928*335850616+1188803754*1578178749+2038502201*331194581+735931834*384407195+1330533011*259537024+1052874750*1634746634+950153811*74403794+1225424092*2001962511+1659116453*465233830+1474177753*480792153+2073609211*323007149+1602919019*2046808035+1865917845*177661286+1085624123*748181341+1837870964*1444239702+1550509101*2026249346+1661725734*2146621927+2066655336*927536095)%2147483647=980358637
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 10 1 3 0 26%2147483647=627064808 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+1849775942*1887634218+656039795*332708175+1840648083*1980751118+246996287*608201127+1369248953*659828919+1132591724*1247578007+92744917*1522110668+1719480363*335850616+1266677922*1578178749+377386917*331194581+735227219*384407195+465096431*259537024+451889791*1634746634+1379836302*74403794+618598847*2001962511+1624084534*465233830+1511477847*480792153+1840812326*323007149+185546252*2046808035+2145463598*177661286+82870699*748181341+1625323762*1444239702+1843639311*2026249346+1777269271*2146621927+1645120956*927536095)%2147483647=627064808
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 10 1 4 0 26%2147483647=1897903933 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+1112406525*1887634218+1345999435*332708175+752376469*1980751118+634588140*608201127+1419170319*659828919+1702860885*1247578007+710076517*1522110668+1256487405*335850616+1114745059*1578178749+1137838899*331194581+1254184109*384407195+1038210451*259537024+274378589*1634746634+171986381*74403794+1536678585*2001962511+1305878831*465233830+1335902916*480792153+1755193245*323007149+2023391453*2046808035+293456010*177661286+1751078325*748181341+1423042536*1444239702+1749638204*2026249346+1345811362*2146621927+1284924881*927536095)%2147483647=1897903933
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 10 1 5 0 26%2147483647=229148989 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+1796814865*1887634218+1253123171*332708175+1317611639*1980751118+1559245386*608201127+1866942376*659828919+1973593402*1247578007+47019780*1522110668+1353487525*335850616+1840161555*1578178749+2003659556*331194581+200559114*384407195+334988447*259537024+2023650872*1634746634+1296497964*74403794+34285357*2001962511+1685894190*465233830+995962325*480792153+1295624230*323007149+1199631211*2046808035+1948677857*177661286+1425322328*748181341+1466877680*1444239702+702011012*2026249346+937706871*2146621927+455802666*927536095)%2147483647=229148989
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 10 1 6 0 26%2147483647=76084977 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+1838939499*1887634218+1353876630*332708175+1258713036*1980751118+1947503436*608201127+1271796599*659828919+1660157177*1247578007+564707688*1522110668+1858113864*335850616+1015817431*1578178749+1264608004*331194581+735383960*384407195+221696734*259537024+1297524163*1634746634+109088572*74403794+792206628*2001962511+1921581249*465233830+94118806*480792153+476103426*323007149+239612482*2046808035+177052717*177661286+826458039*748181341+1923715623*1444239702+1014161165*2026249346+1341609618*2146621927+786325583*927536095)%2147483647=76084977
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 10 1 7 0 26%2147483647=749296556 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*2077540809+418714188*1887634218+1675147475*332708175+1674326661*1980751118+547797802*608201127+2073962627*659828919+897270857*1247578007+1582958967*1522110668+49892701*335850616+1256824732*1578178749+1435903714*331194581+742583315*384407195+1789294768*259537024+13407412*1634746634+518661610*74403794+1259751297*2001962511+1695663205*465233830+2068940067*480792153+940478841*323007149+1982757556*2046808035+1956713516*177661286+863066484*748181341+522298462*1444239702+1343575777*2026249346+771712139*2146621927+157728743*927536095)%2147483647=749296556
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 10 1
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
end AspisR1.JFz_TX2_Q10_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4107579618#u64 2410183778#u64 6194411735#u64 3609006054#u64⟩,⟨pack 2896804495#u64 1162959091#u64 6676030899#u64 2836788307#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5884249082586895912#u64 1421723441176938627#u64 12560321692139308231#u64 4309397818633679599#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 716481079#u32 177557878#u32 1731703130#u32 654297603#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 716481079#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 177557878#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1731703130#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 654297603#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4711145843819218481#u64 971007574937562230#u64 10283948971935943551#u64 4306910731150525272#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 716481079#u32 177557878#u32 1731703130#u32 654297603#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 716481079#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 177557878#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1731703130#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716481079#u32) (JFs_TX2_RawMath.extend 177557878#u32) (JFs_TX2_RawMath.extend 1731703130#u32) (JFs_TX2_RawMath.extend 654297603#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 654297603#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails20.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value0_1=
      ok (.Ok (pack 716481079#u32 177557878#u32 1731703130#u32 654297603#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (716481079<2147483647 ∧ 177557878<2147483647) ∧ (1731703130<2147483647 ∧ 654297603<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 716481079#u32 177557878#u32 1731703130#u32 654297603#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 716481079#u32 177557878#u32 1731703130#u32 654297603#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q10_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4107579618#u64 2410183778#u64 6194411735#u64 3609006054#u64⟩,⟨pack 2896804495#u64 1162959091#u64 6676030899#u64 2836788307#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7502374342#u64 3014864324#u64 13753758052#u64 6642911340#u64⟩,⟨pack 6087132932#u64 1286230708#u64 12351186075#u64 4793292421#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5205619546917719577#u64 289497939582234547#u64 12768253657345856115#u64 3798374857002493161#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 328638817#u32 88738855#u32 1916970252#u32 1328706552#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 328638817#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 88738855#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1916970252#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1328706552#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4802312909396774954#u64 135994373494189422#u64 10241363365192711032#u64 1544599480739747868#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 328638817#u32 88738855#u32 1916970252#u32 1328706552#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 328638817#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 88738855#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1916970252#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 328638817#u32) (JFs_TX2_RawMath.extend 88738855#u32) (JFs_TX2_RawMath.extend 1916970252#u32) (JFs_TX2_RawMath.extend 1328706552#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1328706552#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails20.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value1_1=
      ok (.Ok (pack 328638817#u32 88738855#u32 1916970252#u32 1328706552#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (328638817<2147483647 ∧ 88738855<2147483647) ∧ (1916970252<2147483647 ∧ 1328706552<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 328638817#u32 88738855#u32 1916970252#u32 1328706552#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4107579618#u64 2410183778#u64 6194411735#u64 3609006054#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 328638817#u32 88738855#u32 1916970252#u32 1328706552#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2896804495#u64 1162959091#u64 6676030899#u64 2836788307#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7502374342#u64 3014864324#u64 13753758052#u64 6642911340#u64⟩,⟨pack 6087132932#u64 1286230708#u64 12351186075#u64 4793292421#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10744825407#u64 3664525496#u64 19860683431#u64 8603517941#u64⟩,⟨pack 8248741186#u64 1681707104#u64 18021173704#u64 8236211434#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4472858163885788895#u64 160624924824943595#u64 9100560397389851222#u64 926872242713962688#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 34015989#u32 277716317#u32 705792957#u32 537478294#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 34015989#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 277716317#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 705792957#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 537478294#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4158854665161217453#u64 555808999197719294#u64 9047227627694766590#u64 2911226444890326104#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 34015989#u32 277716317#u32 705792957#u32 537478294#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 34015989#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 277716317#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 705792957#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 34015989#u32) (JFs_TX2_RawMath.extend 277716317#u32) (JFs_TX2_RawMath.extend 705792957#u32) (JFs_TX2_RawMath.extend 537478294#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 537478294#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails20.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value2_1=
      ok (.Ok (pack 34015989#u32 277716317#u32 705792957#u32 537478294#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (34015989<2147483647 ∧ 277716317<2147483647) ∧ (705792957<2147483647 ∧ 537478294<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 34015989#u32 277716317#u32 705792957#u32 537478294#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7502374342#u64 3014864324#u64 13753758052#u64 6642911340#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 34015989#u32 277716317#u32 705792957#u32 537478294#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6087132932#u64 1286230708#u64 12351186075#u64 4793292421#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨7407172#u32,1517041849#u32⟩,⟨533330608#u32,13583353#u32⟩⟩,⟨⟨1806290245#u32,1681707104#u32⟩,⟨841304528#u32,1793760493#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q10_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q10_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10744825407%2147483647 at h0
  norm_num at h0
  have e0 : a0=7407172#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=3664525496%2147483647 at h1
  norm_num at h1
  have e1 : a1=1517041849#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19860683431%2147483647 at h2
  norm_num at h2
  have e2 : a2=533330608#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8603517941%2147483647 at h3
  norm_num at h3
  have e3 : a3=13583353#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8248741186%2147483647 at h4
  norm_num at h4
  have e4 : a4=1806290245#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=1681707104%2147483647 at h5
  norm_num at h5
  have e5 : a5=1681707104#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=18021173704%2147483647 at h6
  norm_num at h6
  have e6 : a6=841304528#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8236211434%2147483647 at h7
  norm_num at h7
  have e7 : a7=1793760493#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q10_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails20.value0_1
      from JFr_TX2_Tails20.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails20.value1_1
      from JFr_TX2_Tails20.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails20.value2_1
      from JFr_TX2_Tails20.source2_1,
    JFz_TX2_Q10_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q10_Raw10.after=JFz_TX2_Q10_Raw11.before := rfl
  have same2 : JFz_TX2_Q10_Raw11.after=JFz_TX2_Q10_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q10_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q10_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q10_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1663637645#u32,423864786#u32⟩,⟨1513689245#u32,640648161#u32⟩⟩,⟨⟨1556710531#u32,1910856093#u32⟩,⟨917389505#u32,395573402#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1663637645<2147483647 ∧ 423864786<2147483647) ∧ (1513689245<2147483647 ∧ 640648161<2147483647)) ∧
    ((1556710531<2147483647 ∧ 1910856093<2147483647) ∧ (917389505<2147483647 ∧ 395573402<2147483647))
  omega
theorem addition : decode JFz_TX2_Q10_Head1.value+decode JFz_TX2_Q10_Tail1.value=decode value := by
  change (⟨⟨⟨1656230473,1054306584⟩,⟨980358637,627064808⟩⟩,⟨⟨1897903933,229148989⟩,⟨76084977,749296556⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨7407172,1517041849⟩,⟨533330608,13583353⟩⟩,⟨⟨1806290245,1681707104⟩,⟨841304528,1793760493⟩⟩⟩=⟨⟨⟨1663637645,423864786⟩,⟨1513689245,640648161⟩⟩,⟨⟨1556710531,1910856093⟩,⟨917389505,395573402⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 10 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q10_Head1.value JFz_TX2_Q10_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q10_Head1.source,
      JFz_TX2_Q10_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q10_Head1.value := by
    change ((1656230473<2147483647 ∧ 1054306584<2147483647) ∧ (980358637<2147483647 ∧ 627064808<2147483647)) ∧
      ((1897903933<2147483647 ∧ 229148989<2147483647) ∧ (76084977<2147483647 ∧ 749296556<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q10_Tail1.value := by
    change ((7407172<2147483647 ∧ 1517041849<2147483647) ∧ (533330608<2147483647 ∧ 13583353<2147483647)) ∧
      ((1806290245<2147483647 ∧ 1681707104<2147483647) ∧ (841304528<2147483647 ∧ 1793760493<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q10_Dot1
end
