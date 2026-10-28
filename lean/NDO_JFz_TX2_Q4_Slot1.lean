import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails14
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1124716773#u32,1636138061#u32⟩,⟨1916090934#u32,1752628419#u32⟩⟩,⟨⟨818097772#u32,853264046#u32⟩,⟨1068817810#u32,172156272#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 4 1 0 0 26%2147483647=1124716773 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*986844344+855639275*34855420+867568255*290628309+352063*490853921+1106523000*1163907483+1554033304*276422543+1430280692*2136328736+1491718280*1578910592+118514350*551265207+1675652887*1612684386+1364884909*1724172441+1135303194*1411533046+304762092*607731936+1465393816*1927573649+824208172*895928673+1752653420*567955442+1385409049*1984174545+1003904973*724601817+1298953245*1593729931+2005758375*1512772964+497936241*1802916118+235809508*101233822+1478307182*1572158623+1858903615*62662457+628035096*864993262+1244951250*1076740187)%2147483647=1124716773
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 4 1 1 0 26%2147483647=1636138061 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+1483149559*34855420+655227887*290628309+39062738*490853921+729079828*1163907483+67370206*276422543+1685049618*2136328736+385547620*1578910592+1786803209*551265207+779721715*1612684386+594709522*1724172441+338788461*1411533046+526756808*607731936+184076238*1927573649+1852498770*895928673+2102463508*567955442+1086671526*1984174545+1147694576*724601817+1504805752*1593729931+2005073905*1512772964+185008025*1802916118+1485990146*101233822+1255280192*1572158623+1018329259*62662457+570157693*864993262+1511904630*1076740187)%2147483647=1636138061
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 4 1 2 0 26%2147483647=1916090934 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+1898717401*34855420+1032732628*290628309+1313565596*490853921+1074182998*1163907483+1410213748*276422543+1182702806*2136328736+321711020*1578910592+2062791928*551265207+1188803754*1612684386+2038502201*1724172441+735931834*1411533046+1330533011*607731936+1052874750*1927573649+950153811*895928673+1225424092*567955442+1659116453*1984174545+1474177753*724601817+2073609211*1593729931+1602919019*1512772964+1865917845*1802916118+1085624123*101233822+1837870964*1572158623+1550509101*62662457+1661725734*864993262+2066655336*1076740187)%2147483647=1916090934
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 4 1 3 0 26%2147483647=1752628419 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+1849775942*34855420+656039795*290628309+1840648083*490853921+246996287*1163907483+1369248953*276422543+1132591724*2136328736+92744917*1578910592+1719480363*551265207+1266677922*1612684386+377386917*1724172441+735227219*1411533046+465096431*607731936+451889791*1927573649+1379836302*895928673+618598847*567955442+1624084534*1984174545+1511477847*724601817+1840812326*1593729931+185546252*1512772964+2145463598*1802916118+82870699*101233822+1625323762*1572158623+1843639311*62662457+1777269271*864993262+1645120956*1076740187)%2147483647=1752628419
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 4 1 4 0 26%2147483647=818097772 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+1112406525*34855420+1345999435*290628309+752376469*490853921+634588140*1163907483+1419170319*276422543+1702860885*2136328736+710076517*1578910592+1256487405*551265207+1114745059*1612684386+1137838899*1724172441+1254184109*1411533046+1038210451*607731936+274378589*1927573649+171986381*895928673+1536678585*567955442+1305878831*1984174545+1335902916*724601817+1755193245*1593729931+2023391453*1512772964+293456010*1802916118+1751078325*101233822+1423042536*1572158623+1749638204*62662457+1345811362*864993262+1284924881*1076740187)%2147483647=818097772
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 4 1 5 0 26%2147483647=853264046 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+1796814865*34855420+1253123171*290628309+1317611639*490853921+1559245386*1163907483+1866942376*276422543+1973593402*2136328736+47019780*1578910592+1353487525*551265207+1840161555*1612684386+2003659556*1724172441+200559114*1411533046+334988447*607731936+2023650872*1927573649+1296497964*895928673+34285357*567955442+1685894190*1984174545+995962325*724601817+1295624230*1593729931+1199631211*1512772964+1948677857*1802916118+1425322328*101233822+1466877680*1572158623+702011012*62662457+937706871*864993262+455802666*1076740187)%2147483647=853264046
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 4 1 6 0 26%2147483647=1068817810 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+1838939499*34855420+1353876630*290628309+1258713036*490853921+1947503436*1163907483+1271796599*276422543+1660157177*2136328736+564707688*1578910592+1858113864*551265207+1015817431*1612684386+1264608004*1724172441+735383960*1411533046+221696734*607731936+1297524163*1927573649+109088572*895928673+792206628*567955442+1921581249*1984174545+94118806*724601817+476103426*1593729931+239612482*1512772964+177052717*1802916118+826458039*101233822+1923715623*1572158623+1014161165*62662457+1341609618*864993262+786325583*1076740187)%2147483647=1068817810
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 4 1 7 0 26%2147483647=172156272 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*986844344+418714188*34855420+1675147475*290628309+1674326661*490853921+547797802*1163907483+2073962627*276422543+897270857*2136328736+1582958967*1578910592+49892701*551265207+1256824732*1612684386+1435903714*1724172441+742583315*1411533046+1789294768*607731936+13407412*1927573649+518661610*895928673+1259751297*567955442+1695663205*1984174545+2068940067*724601817+940478841*1593729931+1982757556*1512772964+1956713516*1802916118+863066484*101233822+522298462*1572158623+1343575777*62662457+771712139*864993262+157728743*1076740187)%2147483647=172156272
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 4 1
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
end AspisR1.JFz_TX2_Q4_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3894415742#u64 2464326959#u64 4251150503#u64 2889644351#u64⟩,⟨pack 3577112318#u64 2288883772#u64 4074529232#u64 3286824002#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5387754223999239591#u64 3845224501409787536#u64 8115860262015254742#u64 4751980236769828749#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1085378277#u32 1060631049#u32 192432490#u32 1480821211#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1085378277#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1060631049#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 192432490#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1480821211#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3777207126269606722#u64 1824987472296560477#u64 7481902136246289692#u64 5343499840319462060#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1085378277#u32 1060631049#u32 192432490#u32 1480821211#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1085378277#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1060631049#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 192432490#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1085378277#u32) (JFs_TX2_RawMath.extend 1060631049#u32) (JFs_TX2_RawMath.extend 192432490#u32) (JFs_TX2_RawMath.extend 1480821211#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1480821211#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails14.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value0_1=
      ok (.Ok (pack 1085378277#u32 1060631049#u32 192432490#u32 1480821211#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1085378277<2147483647 ∧ 1060631049<2147483647) ∧ (192432490<2147483647 ∧ 1480821211<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1085378277#u32 1060631049#u32 192432490#u32 1480821211#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1085378277#u32 1060631049#u32 192432490#u32 1480821211#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q4_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3894415742#u64 2464326959#u64 4251150503#u64 2889644351#u64⟩,⟨pack 3577112318#u64 2288883772#u64 4074529232#u64 3286824002#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7897915348#u64 5397242644#u64 10026337281#u64 6251782844#u64⟩,⟨pack 6384169675#u64 4427281397#u64 9383691161#u64 4412322206#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4286525215517111909#u64 3502988245033452390#u64 10028086744150475732#u64 4505629305624575367#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 175984757#u32 1803933018#u32 1620784061#u32 509848931#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 175984757#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1803933018#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1620784061#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 509848931#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4292737719155199841#u64 1205317663358783403#u64 9197586666996013338#u64 1647222762711647388#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 175984757#u32 1803933018#u32 1620784061#u32 509848931#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 175984757#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1803933018#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1620784061#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 175984757#u32) (JFs_TX2_RawMath.extend 1803933018#u32) (JFs_TX2_RawMath.extend 1620784061#u32) (JFs_TX2_RawMath.extend 509848931#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 509848931#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails14.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value1_1=
      ok (.Ok (pack 175984757#u32 1803933018#u32 1620784061#u32 509848931#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (175984757<2147483647 ∧ 1803933018<2147483647) ∧ (1620784061<2147483647 ∧ 509848931<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 175984757#u32 1803933018#u32 1620784061#u32 509848931#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3894415742#u64 2464326959#u64 4251150503#u64 2889644351#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 175984757#u32 1803933018#u32 1620784061#u32 509848931#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3577112318#u64 2288883772#u64 4074529232#u64 3286824002#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7897915348#u64 5397242644#u64 10026337281#u64 6251782844#u64⟩,⟨pack 6384169675#u64 4427281397#u64 9383691161#u64 4412322206#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11875104280#u64 6236871988#u64 15826268398#u64 8339122669#u64⟩,⟨pack 8337379183#u64 8037116388#u64 15858770281#u64 8659778065#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4161590080106739203#u64 1456341844511148990#u64 9206367397406883888#u64 3050190361587703615#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1023963559#u32 1728285250#u32 1206949774#u32 329215552#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1023963559#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1728285250#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1206949774#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 329215552#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3235418881218483195#u64 4959968585662268323#u64 9773615346487142161#u64 8363940693206739189#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1023963559#u32 1728285250#u32 1206949774#u32 329215552#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1023963559#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1728285250#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1206949774#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1023963559#u32) (JFs_TX2_RawMath.extend 1728285250#u32) (JFs_TX2_RawMath.extend 1206949774#u32) (JFs_TX2_RawMath.extend 329215552#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 329215552#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails14.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value2_1=
      ok (.Ok (pack 1023963559#u32 1728285250#u32 1206949774#u32 329215552#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1023963559<2147483647 ∧ 1728285250<2147483647) ∧ (1206949774<2147483647 ∧ 329215552<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1023963559#u32 1728285250#u32 1206949774#u32 329215552#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7897915348#u64 5397242644#u64 10026337281#u64 6251782844#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1023963559#u32 1728285250#u32 1206949774#u32 329215552#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6384169675#u64 4427281397#u64 9383691161#u64 4412322206#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1137686045#u32,1941904694#u32⟩,⟨793882869#u32,1896671728#u32⟩⟩,⟨⟨1894928242#u32,1594665447#u32⟩,⟨826384752#u32,69843477#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q4_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q4_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11875104280%2147483647 at h0
  norm_num at h0
  have e0 : a0=1137686045#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6236871988%2147483647 at h1
  norm_num at h1
  have e1 : a1=1941904694#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15826268398%2147483647 at h2
  norm_num at h2
  have e2 : a2=793882869#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8339122669%2147483647 at h3
  norm_num at h3
  have e3 : a3=1896671728#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8337379183%2147483647 at h4
  norm_num at h4
  have e4 : a4=1894928242#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=8037116388%2147483647 at h5
  norm_num at h5
  have e5 : a5=1594665447#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15858770281%2147483647 at h6
  norm_num at h6
  have e6 : a6=826384752#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8659778065%2147483647 at h7
  norm_num at h7
  have e7 : a7=69843477#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q4_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails14.value0_1
      from JFr_TX2_Tails14.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails14.value1_1
      from JFr_TX2_Tails14.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails14.value2_1
      from JFr_TX2_Tails14.source2_1,
    JFz_TX2_Q4_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q4_Raw10.after=JFz_TX2_Q4_Raw11.before := rfl
  have same2 : JFz_TX2_Q4_Raw11.after=JFz_TX2_Q4_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q4_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q4_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q4_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨114919171#u32,1430559108#u32⟩,⟨562490156#u32,1501816500#u32⟩⟩,⟨⟨565542367#u32,300445846#u32⟩,⟨1895202562#u32,241999749#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((114919171<2147483647 ∧ 1430559108<2147483647) ∧ (562490156<2147483647 ∧ 1501816500<2147483647)) ∧
    ((565542367<2147483647 ∧ 300445846<2147483647) ∧ (1895202562<2147483647 ∧ 241999749<2147483647))
  omega
theorem addition : decode JFz_TX2_Q4_Head1.value+decode JFz_TX2_Q4_Tail1.value=decode value := by
  change (⟨⟨⟨1124716773,1636138061⟩,⟨1916090934,1752628419⟩⟩,⟨⟨818097772,853264046⟩,⟨1068817810,172156272⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1137686045,1941904694⟩,⟨793882869,1896671728⟩⟩,⟨⟨1894928242,1594665447⟩,⟨826384752,69843477⟩⟩⟩=⟨⟨⟨114919171,1430559108⟩,⟨562490156,1501816500⟩⟩,⟨⟨565542367,300445846⟩,⟨1895202562,241999749⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 4 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q4_Head1.value JFz_TX2_Q4_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q4_Head1.source,
      JFz_TX2_Q4_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q4_Head1.value := by
    change ((1124716773<2147483647 ∧ 1636138061<2147483647) ∧ (1916090934<2147483647 ∧ 1752628419<2147483647)) ∧
      ((818097772<2147483647 ∧ 853264046<2147483647) ∧ (1068817810<2147483647 ∧ 172156272<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q4_Tail1.value := by
    change ((1137686045<2147483647 ∧ 1941904694<2147483647) ∧ (793882869<2147483647 ∧ 1896671728<2147483647)) ∧
      ((1894928242<2147483647 ∧ 1594665447<2147483647) ∧ (826384752<2147483647 ∧ 69843477<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q4_Dot1
end
