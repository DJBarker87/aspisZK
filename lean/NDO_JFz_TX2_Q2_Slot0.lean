import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails12
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨838238705#u32,2094513991#u32⟩,⟨1345062150#u32,800937702#u32⟩⟩,⟨⟨1026510654#u32,1469652119#u32⟩,⟨1726290208#u32,347946543#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 2 0 0 0 26%2147483647=838238705 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*691280594+855639275*1989042579+867568255*617971687+352063*1984955641+1106523000*1318955700+1554033304*1483071370+1430280692*521303406+1491718280*1581056970+118514350*966642231+1675652887*1841595221+1364884909*1207812337+1135303194*423175339+304762092*1575304568+1465393816*796154398+824208172*1372036943+1752653420*1459680128+1385409049*1185208990+1003904973*1362505776+1298953245*203978642+2005758375*545857630+497936241*1264031676+235809508*632598605+1478307182*1604914597+1858903615*1428742844+628035096*1899194244+1244951250*1317923578)%2147483647=838238705
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 2 0 1 0 26%2147483647=2094513991 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+1483149559*1989042579+655227887*617971687+39062738*1984955641+729079828*1318955700+67370206*1483071370+1685049618*521303406+385547620*1581056970+1786803209*966642231+779721715*1841595221+594709522*1207812337+338788461*423175339+526756808*1575304568+184076238*796154398+1852498770*1372036943+2102463508*1459680128+1086671526*1185208990+1147694576*1362505776+1504805752*203978642+2005073905*545857630+185008025*1264031676+1485990146*632598605+1255280192*1604914597+1018329259*1428742844+570157693*1899194244+1511904630*1317923578)%2147483647=2094513991
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 2 0 2 0 26%2147483647=1345062150 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+1898717401*1989042579+1032732628*617971687+1313565596*1984955641+1074182998*1318955700+1410213748*1483071370+1182702806*521303406+321711020*1581056970+2062791928*966642231+1188803754*1841595221+2038502201*1207812337+735931834*423175339+1330533011*1575304568+1052874750*796154398+950153811*1372036943+1225424092*1459680128+1659116453*1185208990+1474177753*1362505776+2073609211*203978642+1602919019*545857630+1865917845*1264031676+1085624123*632598605+1837870964*1604914597+1550509101*1428742844+1661725734*1899194244+2066655336*1317923578)%2147483647=1345062150
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 2 0 3 0 26%2147483647=800937702 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+1849775942*1989042579+656039795*617971687+1840648083*1984955641+246996287*1318955700+1369248953*1483071370+1132591724*521303406+92744917*1581056970+1719480363*966642231+1266677922*1841595221+377386917*1207812337+735227219*423175339+465096431*1575304568+451889791*796154398+1379836302*1372036943+618598847*1459680128+1624084534*1185208990+1511477847*1362505776+1840812326*203978642+185546252*545857630+2145463598*1264031676+82870699*632598605+1625323762*1604914597+1843639311*1428742844+1777269271*1899194244+1645120956*1317923578)%2147483647=800937702
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 2 0 4 0 26%2147483647=1026510654 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+1112406525*1989042579+1345999435*617971687+752376469*1984955641+634588140*1318955700+1419170319*1483071370+1702860885*521303406+710076517*1581056970+1256487405*966642231+1114745059*1841595221+1137838899*1207812337+1254184109*423175339+1038210451*1575304568+274378589*796154398+171986381*1372036943+1536678585*1459680128+1305878831*1185208990+1335902916*1362505776+1755193245*203978642+2023391453*545857630+293456010*1264031676+1751078325*632598605+1423042536*1604914597+1749638204*1428742844+1345811362*1899194244+1284924881*1317923578)%2147483647=1026510654
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 2 0 5 0 26%2147483647=1469652119 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+1796814865*1989042579+1253123171*617971687+1317611639*1984955641+1559245386*1318955700+1866942376*1483071370+1973593402*521303406+47019780*1581056970+1353487525*966642231+1840161555*1841595221+2003659556*1207812337+200559114*423175339+334988447*1575304568+2023650872*796154398+1296497964*1372036943+34285357*1459680128+1685894190*1185208990+995962325*1362505776+1295624230*203978642+1199631211*545857630+1948677857*1264031676+1425322328*632598605+1466877680*1604914597+702011012*1428742844+937706871*1899194244+455802666*1317923578)%2147483647=1469652119
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 2 0 6 0 26%2147483647=1726290208 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+1838939499*1989042579+1353876630*617971687+1258713036*1984955641+1947503436*1318955700+1271796599*1483071370+1660157177*521303406+564707688*1581056970+1858113864*966642231+1015817431*1841595221+1264608004*1207812337+735383960*423175339+221696734*1575304568+1297524163*796154398+109088572*1372036943+792206628*1459680128+1921581249*1185208990+94118806*1362505776+476103426*203978642+239612482*545857630+177052717*1264031676+826458039*632598605+1923715623*1604914597+1014161165*1428742844+1341609618*1899194244+786325583*1317923578)%2147483647=1726290208
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 2 0 7 0 26%2147483647=347946543 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*691280594+418714188*1989042579+1675147475*617971687+1674326661*1984955641+547797802*1318955700+2073962627*1483071370+897270857*521303406+1582958967*1581056970+49892701*966642231+1256824732*1841595221+1435903714*1207812337+742583315*423175339+1789294768*1575304568+13407412*796154398+518661610*1372036943+1259751297*1459680128+1695663205*1185208990+2068940067*1362505776+940478841*203978642+1982757556*545857630+1956713516*1264031676+863066484*632598605+522298462*1604914597+1343575777*1428742844+771712139*1899194244+157728743*1317923578)%2147483647=347946543
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 2 0
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
end AspisR1.JFz_TX2_Q2_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2695279163#u64 2898460516#u64 5733162439#u64 3500722056#u64⟩,⟨pack 2946930098#u64 1297672478#u64 5195814192#u64 4053168006#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 3655299493121899312#u64 2965529521877656734#u64 10035655356948774663#u64 3243913784760165052#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 339850432#u32 1156530904#u32 736656496#u32 476933189#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 339850432#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1156530904#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 736656496#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 476933189#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3324461523528637802#u64 940126083771066812#u64 7244013135280080399#u64 4213216085272804381#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 339850432#u32 1156530904#u32 736656496#u32 476933189#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 339850432#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1156530904#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 736656496#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 339850432#u32) (JFs_TX2_RawMath.extend 1156530904#u32) (JFs_TX2_RawMath.extend 736656496#u32) (JFs_TX2_RawMath.extend 476933189#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 476933189#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails12.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value0_0=
      ok (.Ok (pack 339850432#u32 1156530904#u32 736656496#u32 476933189#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (339850432<2147483647 ∧ 1156530904<2147483647) ∧ (736656496<2147483647 ∧ 476933189<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 339850432#u32 1156530904#u32 736656496#u32 476933189#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 339850432#u32 1156530904#u32 736656496#u32 476933189#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q2_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2695279163#u64 2898460516#u64 5733162439#u64 3500722056#u64⟩,⟨pack 2946930098#u64 1297672478#u64 5195814192#u64 4053168006#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6157048635#u64 6175633186#u64 11213191286#u64 7861589151#u64⟩,⟨pack 6898956360#u64 2250639397#u64 11499409532#u64 5813606250#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6681180877523108808#u64 3821042356741180464#u64 11195623332284525178#u64 6356443149409209948#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1418469377#u32 1732085251#u32 1251825952#u32 754711633#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1418469377#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1732085251#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1251825952#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 754711633#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5111084405346185783#u64 1456826739989528224#u64 9513351134436970085#u64 2392732027914077616#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1418469377#u32 1732085251#u32 1251825952#u32 754711633#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1418469377#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1732085251#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1251825952#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1418469377#u32) (JFs_TX2_RawMath.extend 1732085251#u32) (JFs_TX2_RawMath.extend 1251825952#u32) (JFs_TX2_RawMath.extend 754711633#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 754711633#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails12.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value1_0=
      ok (.Ok (pack 1418469377#u32 1732085251#u32 1251825952#u32 754711633#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1418469377<2147483647 ∧ 1732085251<2147483647) ∧ (1251825952<2147483647 ∧ 754711633<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1418469377#u32 1732085251#u32 1251825952#u32 754711633#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2695279163#u64 2898460516#u64 5733162439#u64 3500722056#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1418469377#u32 1732085251#u32 1251825952#u32 754711633#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2946930098#u64 1297672478#u64 5195814192#u64 4053168006#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6157048635#u64 6175633186#u64 11213191286#u64 7861589151#u64⟩,⟨pack 6898956360#u64 2250639397#u64 11499409532#u64 5813606250#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8888964442#u64 7099023208#u64 17196472800#u64 10699484324#u64⟩,⟨pack 9324905507#u64 5818177024#u64 17121166943#u64 12754516110#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4037428626000843324#u64 1760745141148776325#u64 9006645639540740208#u64 4427888795056131385#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1211371114#u32 2118908611#u32 2043223757#u32 1197534136#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1211371114#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2118908611#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2043223757#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1197534136#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2846210495992135968#u64 5999650700003260623#u64 9337404476399220247#u64 12624291607925023867#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1211371114#u32 2118908611#u32 2043223757#u32 1197534136#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1211371114#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2118908611#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2043223757#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1211371114#u32) (JFs_TX2_RawMath.extend 2118908611#u32) (JFs_TX2_RawMath.extend 2043223757#u32) (JFs_TX2_RawMath.extend 1197534136#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1197534136#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails12.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value2_0=
      ok (.Ok (pack 1211371114#u32 2118908611#u32 2043223757#u32 1197534136#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1211371114<2147483647 ∧ 2118908611<2147483647) ∧ (2043223757<2147483647 ∧ 1197534136<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1211371114#u32 2118908611#u32 2043223757#u32 1197534136#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6157048635#u64 6175633186#u64 11213191286#u64 7861589151#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1211371114#u32 2118908611#u32 2043223757#u32 1197534136#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6898956360#u64 2250639397#u64 11499409532#u64 5813606250#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨299029854#u32,656572267#u32⟩,⟨16603624#u32,2109549736#u32⟩⟩,⟨⟨734970919#u32,1523209730#u32⟩,⟨2088781414#u32,2017097875#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q2_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q2_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=8888964442%2147483647 at h0
  norm_num at h0
  have e0 : a0=299029854#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7099023208%2147483647 at h1
  norm_num at h1
  have e1 : a1=656572267#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17196472800%2147483647 at h2
  norm_num at h2
  have e2 : a2=16603624#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10699484324%2147483647 at h3
  norm_num at h3
  have e3 : a3=2109549736#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9324905507%2147483647 at h4
  norm_num at h4
  have e4 : a4=734970919#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5818177024%2147483647 at h5
  norm_num at h5
  have e5 : a5=1523209730#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17121166943%2147483647 at h6
  norm_num at h6
  have e6 : a6=2088781414#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12754516110%2147483647 at h7
  norm_num at h7
  have e7 : a7=2017097875#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q2_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails12.value0_0
      from JFr_TX2_Tails12.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails12.value1_0
      from JFr_TX2_Tails12.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails12.value2_0
      from JFr_TX2_Tails12.source2_0,
    JFz_TX2_Q2_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q2_Raw00.after=JFz_TX2_Q2_Raw01.before := rfl
  have same2 : JFz_TX2_Q2_Raw01.after=JFz_TX2_Q2_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q2_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q2_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q2_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1137268559#u32,603602611#u32⟩,⟨1361665774#u32,763003791#u32⟩⟩,⟨⟨1761481573#u32,845378202#u32⟩,⟨1667587975#u32,217560771#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1137268559<2147483647 ∧ 603602611<2147483647) ∧ (1361665774<2147483647 ∧ 763003791<2147483647)) ∧
    ((1761481573<2147483647 ∧ 845378202<2147483647) ∧ (1667587975<2147483647 ∧ 217560771<2147483647))
  omega
theorem addition : decode JFz_TX2_Q2_Head0.value+decode JFz_TX2_Q2_Tail0.value=decode value := by
  change (⟨⟨⟨838238705,2094513991⟩,⟨1345062150,800937702⟩⟩,⟨⟨1026510654,1469652119⟩,⟨1726290208,347946543⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨299029854,656572267⟩,⟨16603624,2109549736⟩⟩,⟨⟨734970919,1523209730⟩,⟨2088781414,2017097875⟩⟩⟩=⟨⟨⟨1137268559,603602611⟩,⟨1361665774,763003791⟩⟩,⟨⟨1761481573,845378202⟩,⟨1667587975,217560771⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 2 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q2_Head0.value JFz_TX2_Q2_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q2_Head0.source,
      JFz_TX2_Q2_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q2_Head0.value := by
    change ((838238705<2147483647 ∧ 2094513991<2147483647) ∧ (1345062150<2147483647 ∧ 800937702<2147483647)) ∧
      ((1026510654<2147483647 ∧ 1469652119<2147483647) ∧ (1726290208<2147483647 ∧ 347946543<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q2_Tail0.value := by
    change ((299029854<2147483647 ∧ 656572267<2147483647) ∧ (16603624<2147483647 ∧ 2109549736<2147483647)) ∧
      ((734970919<2147483647 ∧ 1523209730<2147483647) ∧ (2088781414<2147483647 ∧ 2017097875<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q2_Dot0
end
