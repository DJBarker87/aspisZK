import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails15
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨157636032#u32,474514066#u32⟩,⟨367136174#u32,1303961141#u32⟩⟩,⟨⟨1591045496#u32,1153641111#u32⟩,⟨1901742622#u32,1922738172#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 5 0 0 0 26%2147483647=157636032 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*233395674+855639275*396977524+867568255*1894806738+352063*417710234+1106523000*174763491+1554033304*1833684756+1430280692*1462667919+1491718280*1766357342+118514350*429664168+1675652887*996107379+1364884909*1238098396+1135303194*1133843383+304762092*734679870+1465393816*75969118+824208172*513908742+1752653420*1758766575+1385409049*157185903+1003904973*2002898981+1298953245*1007798328+2005758375*1865947523+497936241*1540390899+235809508*1262719792+1478307182*1638051267+1858903615*858202200+628035096*395849199+1244951250*351159355)%2147483647=157636032
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 5 0 1 0 26%2147483647=474514066 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+1483149559*396977524+655227887*1894806738+39062738*417710234+729079828*174763491+67370206*1833684756+1685049618*1462667919+385547620*1766357342+1786803209*429664168+779721715*996107379+594709522*1238098396+338788461*1133843383+526756808*734679870+184076238*75969118+1852498770*513908742+2102463508*1758766575+1086671526*157185903+1147694576*2002898981+1504805752*1007798328+2005073905*1865947523+185008025*1540390899+1485990146*1262719792+1255280192*1638051267+1018329259*858202200+570157693*395849199+1511904630*351159355)%2147483647=474514066
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 5 0 2 0 26%2147483647=367136174 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+1898717401*396977524+1032732628*1894806738+1313565596*417710234+1074182998*174763491+1410213748*1833684756+1182702806*1462667919+321711020*1766357342+2062791928*429664168+1188803754*996107379+2038502201*1238098396+735931834*1133843383+1330533011*734679870+1052874750*75969118+950153811*513908742+1225424092*1758766575+1659116453*157185903+1474177753*2002898981+2073609211*1007798328+1602919019*1865947523+1865917845*1540390899+1085624123*1262719792+1837870964*1638051267+1550509101*858202200+1661725734*395849199+2066655336*351159355)%2147483647=367136174
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 5 0 3 0 26%2147483647=1303961141 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+1849775942*396977524+656039795*1894806738+1840648083*417710234+246996287*174763491+1369248953*1833684756+1132591724*1462667919+92744917*1766357342+1719480363*429664168+1266677922*996107379+377386917*1238098396+735227219*1133843383+465096431*734679870+451889791*75969118+1379836302*513908742+618598847*1758766575+1624084534*157185903+1511477847*2002898981+1840812326*1007798328+185546252*1865947523+2145463598*1540390899+82870699*1262719792+1625323762*1638051267+1843639311*858202200+1777269271*395849199+1645120956*351159355)%2147483647=1303961141
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 5 0 4 0 26%2147483647=1591045496 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+1112406525*396977524+1345999435*1894806738+752376469*417710234+634588140*174763491+1419170319*1833684756+1702860885*1462667919+710076517*1766357342+1256487405*429664168+1114745059*996107379+1137838899*1238098396+1254184109*1133843383+1038210451*734679870+274378589*75969118+171986381*513908742+1536678585*1758766575+1305878831*157185903+1335902916*2002898981+1755193245*1007798328+2023391453*1865947523+293456010*1540390899+1751078325*1262719792+1423042536*1638051267+1749638204*858202200+1345811362*395849199+1284924881*351159355)%2147483647=1591045496
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 5 0 5 0 26%2147483647=1153641111 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+1796814865*396977524+1253123171*1894806738+1317611639*417710234+1559245386*174763491+1866942376*1833684756+1973593402*1462667919+47019780*1766357342+1353487525*429664168+1840161555*996107379+2003659556*1238098396+200559114*1133843383+334988447*734679870+2023650872*75969118+1296497964*513908742+34285357*1758766575+1685894190*157185903+995962325*2002898981+1295624230*1007798328+1199631211*1865947523+1948677857*1540390899+1425322328*1262719792+1466877680*1638051267+702011012*858202200+937706871*395849199+455802666*351159355)%2147483647=1153641111
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 5 0 6 0 26%2147483647=1901742622 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+1838939499*396977524+1353876630*1894806738+1258713036*417710234+1947503436*174763491+1271796599*1833684756+1660157177*1462667919+564707688*1766357342+1858113864*429664168+1015817431*996107379+1264608004*1238098396+735383960*1133843383+221696734*734679870+1297524163*75969118+109088572*513908742+792206628*1758766575+1921581249*157185903+94118806*2002898981+476103426*1007798328+239612482*1865947523+177052717*1540390899+826458039*1262719792+1923715623*1638051267+1014161165*858202200+1341609618*395849199+786325583*351159355)%2147483647=1901742622
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 5 0 7 0 26%2147483647=1922738172 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*233395674+418714188*396977524+1675147475*1894806738+1674326661*417710234+547797802*174763491+2073962627*1833684756+897270857*1462667919+1582958967*1766357342+49892701*429664168+1256824732*996107379+1435903714*1238098396+742583315*1133843383+1789294768*734679870+13407412*75969118+518661610*513908742+1259751297*1758766575+1695663205*157185903+2068940067*2002898981+940478841*1007798328+1982757556*1865947523+1956713516*1540390899+863066484*1262719792+522298462*1638051267+1343575777*858202200+771712139*395849199+157728743*351159355)%2147483647=1922738172
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 5 0
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
end AspisR1.JFz_TX2_Q5_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3729058455#u64 1124657610#u64 6588937532#u64 2974102628#u64⟩,⟨pack 3516726034#u64 835053842#u64 4786420348#u64 1829114749#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4270134657976092902#u64 1520321904548143195#u64 9582940024475767521#u64 2959152837698988221#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 221796964#u32 560524521#u32 627610075#u32 687392014#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 221796964#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 560524521#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 627610075#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 687392014#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4013348377255767271#u64 526679313826160891#u64 7934492634915079286#u64 2701830584929905225#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 221796964#u32 560524521#u32 627610075#u32 687392014#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 221796964#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 560524521#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 627610075#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 221796964#u32) (JFs_TX2_RawMath.extend 560524521#u32) (JFs_TX2_RawMath.extend 627610075#u32) (JFs_TX2_RawMath.extend 687392014#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 687392014#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails15.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value0_0=
      ok (.Ok (pack 221796964#u32 560524521#u32 627610075#u32 687392014#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (221796964<2147483647 ∧ 560524521<2147483647) ∧ (627610075<2147483647 ∧ 687392014<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 221796964#u32 560524521#u32 627610075#u32 687392014#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 221796964#u32 560524521#u32 627610075#u32 687392014#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q5_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3729058455#u64 1124657610#u64 6588937532#u64 2974102628#u64⟩,⟨pack 3516726034#u64 835053842#u64 4786420348#u64 1829114749#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7527977021#u64 3032742704#u64 12862673140#u64 6679129549#u64⟩,⟨pack 7094460267#u64 2326750204#u64 11082857213#u64 3109483727#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6444170606753763226#u64 1726923823028930884#u64 10974372555398840405#u64 6033666965663281443#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1095001353#u32 695610103#u32 860125412#u32 1699666990#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1095001353#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 695610103#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 860125412#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1699666990#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5150972474900875264#u64 710994341948919742#u64 9477068187032969702#u64 2246894853893110628#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1095001353#u32 695610103#u32 860125412#u32 1699666990#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1095001353#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 695610103#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 860125412#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1095001353#u32) (JFs_TX2_RawMath.extend 695610103#u32) (JFs_TX2_RawMath.extend 860125412#u32) (JFs_TX2_RawMath.extend 1699666990#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1699666990#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails15.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value1_0=
      ok (.Ok (pack 1095001353#u32 695610103#u32 860125412#u32 1699666990#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1095001353<2147483647 ∧ 695610103<2147483647) ∧ (860125412<2147483647 ∧ 1699666990<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1095001353#u32 695610103#u32 860125412#u32 1699666990#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3729058455#u64 1124657610#u64 6588937532#u64 2974102628#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1095001353#u32 695610103#u32 860125412#u32 1699666990#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3516726034#u64 835053842#u64 4786420348#u64 1829114749#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7527977021#u64 3032742704#u64 12862673140#u64 6679129549#u64⟩,⟨pack 7094460267#u64 2326750204#u64 11082857213#u64 3109483727#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10752376513#u64 5318311882#u64 17668872294#u64 8289652675#u64⟩,⟨pack 12012812580#u64 5845190270#u64 16109352573#u64 8136619538#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5281211456453028567#u64 1578261529901190043#u64 9735640450890523809#u64 3425621876857774097#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2133788062#u32 742756322#u32 557598471#u32 1754125920#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2133788062#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 742756322#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 557598471#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1754125920#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 7026588932664012522#u64 5261563748756060622#u64 10151257802574214432#u64 9627276652462348044#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2133788062#u32 742756322#u32 557598471#u32 1754125920#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2133788062#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 742756322#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 557598471#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2133788062#u32) (JFs_TX2_RawMath.extend 742756322#u32) (JFs_TX2_RawMath.extend 557598471#u32) (JFs_TX2_RawMath.extend 1754125920#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1754125920#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails15.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value2_0=
      ok (.Ok (pack 2133788062#u32 742756322#u32 557598471#u32 1754125920#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2133788062<2147483647 ∧ 742756322<2147483647) ∧ (557598471<2147483647 ∧ 1754125920<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2133788062#u32 742756322#u32 557598471#u32 1754125920#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7527977021#u64 3032742704#u64 12862673140#u64 6679129549#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2133788062#u32 742756322#u32 557598471#u32 1754125920#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7094460267#u64 2326750204#u64 11082857213#u64 3109483727#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨14958278#u32,1023344588#u32⟩,⟨489003118#u32,1847201734#u32⟩⟩,⟨⟨1275394345#u32,1550222976#u32⟩,⟨1076967044#u32,1694168597#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q5_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q5_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10752376513%2147483647 at h0
  norm_num at h0
  have e0 : a0=14958278#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5318311882%2147483647 at h1
  norm_num at h1
  have e1 : a1=1023344588#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17668872294%2147483647 at h2
  norm_num at h2
  have e2 : a2=489003118#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8289652675%2147483647 at h3
  norm_num at h3
  have e3 : a3=1847201734#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=12012812580%2147483647 at h4
  norm_num at h4
  have e4 : a4=1275394345#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5845190270%2147483647 at h5
  norm_num at h5
  have e5 : a5=1550222976#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16109352573%2147483647 at h6
  norm_num at h6
  have e6 : a6=1076967044#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8136619538%2147483647 at h7
  norm_num at h7
  have e7 : a7=1694168597#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q5_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails15.value0_0
      from JFr_TX2_Tails15.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails15.value1_0
      from JFr_TX2_Tails15.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails15.value2_0
      from JFr_TX2_Tails15.source2_0,
    JFz_TX2_Q5_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q5_Raw00.after=JFz_TX2_Q5_Raw01.before := rfl
  have same2 : JFz_TX2_Q5_Raw01.after=JFz_TX2_Q5_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q5_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q5_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q5_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨172594310#u32,1497858654#u32⟩,⟨856139292#u32,1003679228#u32⟩⟩,⟨⟨718956194#u32,556380440#u32⟩,⟨831226019#u32,1469423122#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((172594310<2147483647 ∧ 1497858654<2147483647) ∧ (856139292<2147483647 ∧ 1003679228<2147483647)) ∧
    ((718956194<2147483647 ∧ 556380440<2147483647) ∧ (831226019<2147483647 ∧ 1469423122<2147483647))
  omega
theorem addition : decode JFz_TX2_Q5_Head0.value+decode JFz_TX2_Q5_Tail0.value=decode value := by
  change (⟨⟨⟨157636032,474514066⟩,⟨367136174,1303961141⟩⟩,⟨⟨1591045496,1153641111⟩,⟨1901742622,1922738172⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨14958278,1023344588⟩,⟨489003118,1847201734⟩⟩,⟨⟨1275394345,1550222976⟩,⟨1076967044,1694168597⟩⟩⟩=⟨⟨⟨172594310,1497858654⟩,⟨856139292,1003679228⟩⟩,⟨⟨718956194,556380440⟩,⟨831226019,1469423122⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 5 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q5_Head0.value JFz_TX2_Q5_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q5_Head0.source,
      JFz_TX2_Q5_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q5_Head0.value := by
    change ((157636032<2147483647 ∧ 474514066<2147483647) ∧ (367136174<2147483647 ∧ 1303961141<2147483647)) ∧
      ((1591045496<2147483647 ∧ 1153641111<2147483647) ∧ (1901742622<2147483647 ∧ 1922738172<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q5_Tail0.value := by
    change ((14958278<2147483647 ∧ 1023344588<2147483647) ∧ (489003118<2147483647 ∧ 1847201734<2147483647)) ∧
      ((1275394345<2147483647 ∧ 1550222976<2147483647) ∧ (1076967044<2147483647 ∧ 1694168597<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q5_Dot0
end
