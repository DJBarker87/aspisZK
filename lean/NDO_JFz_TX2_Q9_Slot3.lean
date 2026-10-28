import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails19
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1974236771#u32,1171804387#u32⟩,⟨1738127542#u32,748157662#u32⟩⟩,⟨⟨1930801052#u32,169303785#u32⟩,⟨641549610#u32,702887363#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 9 3 0 0 26%2147483647=1974236771 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1148690029+855639275*270855777+867568255*1976609050+352063*1454680926+1106523000*1467469948+1554033304*965116586+1430280692*679974775+1491718280*1945336273+118514350*2010274249+1675652887*1058990437+1364884909*2099708231+1135303194*2128036206+304762092*1171852094+1465393816*994593120+824208172*847094679+1752653420*1521290848+1385409049*1334140563+1003904973*1872578515+1298953245*1315782306+2005758375*2074657127+497936241*211967328+235809508*1338416151+1478307182*488568360+1858903615*421944197+628035096*1436712463+1244951250*181649598)%2147483647=1974236771
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 9 3 1 0 26%2147483647=1171804387 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+1483149559*270855777+655227887*1976609050+39062738*1454680926+729079828*1467469948+67370206*965116586+1685049618*679974775+385547620*1945336273+1786803209*2010274249+779721715*1058990437+594709522*2099708231+338788461*2128036206+526756808*1171852094+184076238*994593120+1852498770*847094679+2102463508*1521290848+1086671526*1334140563+1147694576*1872578515+1504805752*1315782306+2005073905*2074657127+185008025*211967328+1485990146*1338416151+1255280192*488568360+1018329259*421944197+570157693*1436712463+1511904630*181649598)%2147483647=1171804387
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 9 3 2 0 26%2147483647=1738127542 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+1898717401*270855777+1032732628*1976609050+1313565596*1454680926+1074182998*1467469948+1410213748*965116586+1182702806*679974775+321711020*1945336273+2062791928*2010274249+1188803754*1058990437+2038502201*2099708231+735931834*2128036206+1330533011*1171852094+1052874750*994593120+950153811*847094679+1225424092*1521290848+1659116453*1334140563+1474177753*1872578515+2073609211*1315782306+1602919019*2074657127+1865917845*211967328+1085624123*1338416151+1837870964*488568360+1550509101*421944197+1661725734*1436712463+2066655336*181649598)%2147483647=1738127542
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 9 3 3 0 26%2147483647=748157662 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+1849775942*270855777+656039795*1976609050+1840648083*1454680926+246996287*1467469948+1369248953*965116586+1132591724*679974775+92744917*1945336273+1719480363*2010274249+1266677922*1058990437+377386917*2099708231+735227219*2128036206+465096431*1171852094+451889791*994593120+1379836302*847094679+618598847*1521290848+1624084534*1334140563+1511477847*1872578515+1840812326*1315782306+185546252*2074657127+2145463598*211967328+82870699*1338416151+1625323762*488568360+1843639311*421944197+1777269271*1436712463+1645120956*181649598)%2147483647=748157662
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 9 3 4 0 26%2147483647=1930801052 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+1112406525*270855777+1345999435*1976609050+752376469*1454680926+634588140*1467469948+1419170319*965116586+1702860885*679974775+710076517*1945336273+1256487405*2010274249+1114745059*1058990437+1137838899*2099708231+1254184109*2128036206+1038210451*1171852094+274378589*994593120+171986381*847094679+1536678585*1521290848+1305878831*1334140563+1335902916*1872578515+1755193245*1315782306+2023391453*2074657127+293456010*211967328+1751078325*1338416151+1423042536*488568360+1749638204*421944197+1345811362*1436712463+1284924881*181649598)%2147483647=1930801052
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 9 3 5 0 26%2147483647=169303785 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+1796814865*270855777+1253123171*1976609050+1317611639*1454680926+1559245386*1467469948+1866942376*965116586+1973593402*679974775+47019780*1945336273+1353487525*2010274249+1840161555*1058990437+2003659556*2099708231+200559114*2128036206+334988447*1171852094+2023650872*994593120+1296497964*847094679+34285357*1521290848+1685894190*1334140563+995962325*1872578515+1295624230*1315782306+1199631211*2074657127+1948677857*211967328+1425322328*1338416151+1466877680*488568360+702011012*421944197+937706871*1436712463+455802666*181649598)%2147483647=169303785
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 9 3 6 0 26%2147483647=641549610 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+1838939499*270855777+1353876630*1976609050+1258713036*1454680926+1947503436*1467469948+1271796599*965116586+1660157177*679974775+564707688*1945336273+1858113864*2010274249+1015817431*1058990437+1264608004*2099708231+735383960*2128036206+221696734*1171852094+1297524163*994593120+109088572*847094679+792206628*1521290848+1921581249*1334140563+94118806*1872578515+476103426*1315782306+239612482*2074657127+177052717*211967328+826458039*1338416151+1923715623*488568360+1014161165*421944197+1341609618*1436712463+786325583*181649598)%2147483647=641549610
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 9 3 7 0 26%2147483647=702887363 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1148690029+418714188*270855777+1675147475*1976609050+1674326661*1454680926+547797802*1467469948+2073962627*965116586+897270857*679974775+1582958967*1945336273+49892701*2010274249+1256824732*1058990437+1435903714*2099708231+742583315*2128036206+1789294768*1171852094+13407412*994593120+518661610*847094679+1259751297*1521290848+1695663205*1334140563+2068940067*1872578515+940478841*1315782306+1982757556*2074657127+1956713516*211967328+863066484*1338416151+522298462*488568360+1343575777*421944197+771712139*1436712463+157728743*181649598)%2147483647=702887363
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 9)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 9 3
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
end AspisR1.JFz_TX2_Q9_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3277691812#u64 2112828276#u64 6777176762#u64 6395788079#u64⟩,⟨pack 1251449952#u64 864480817#u64 3389075130#u64 4680503633#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 2469625488173292813#u64 4145703035024061840#u64 10264842857274370648#u64 9208985839845913479#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 217659248#u32 1792073715#u32 2093540169#u32 2095056979#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 217659248#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1792073715#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2093540169#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2095056979#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2478935459116988171#u64 1072288995842710495#u64 4260384759756182527#u64 7675112969297189928#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 217659248#u32 1792073715#u32 2093540169#u32 2095056979#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 217659248#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1792073715#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2093540169#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 217659248#u32) (JFs_TX2_RawMath.extend 1792073715#u32) (JFs_TX2_RawMath.extend 2093540169#u32) (JFs_TX2_RawMath.extend 2095056979#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2095056979#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails19.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails19.value0_3=
      ok (.Ok (pack 217659248#u32 1792073715#u32 2093540169#u32 2095056979#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (217659248<2147483647 ∧ 1792073715<2147483647) ∧ (2093540169<2147483647 ∧ 2095056979<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 217659248#u32 1792073715#u32 2093540169#u32 2095056979#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 217659248#u32 1792073715#u32 2093540169#u32 2095056979#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q9_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3277691812#u64 2112828276#u64 6777176762#u64 6395788079#u64⟩,⟨pack 1251449952#u64 864480817#u64 3389075130#u64 4680503633#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7074832398#u64 4724150306#u64 13054141283#u64 9622465381#u64⟩,⟨pack 3943839558#u64 3299558946#u64 8868906247#u64 6790062129#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 8014859709743809416#u64 3281537589992022676#u64 11162720988801464696#u64 6846614025938866649#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2040799097#u32 1329487598#u32 522665344#u32 1041667360#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2040799097#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1329487598#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 522665344#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1041667360#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5608853901379718422#u64 1346419530528027926#u64 9490365454350711835#u64 2573010323343865949#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2040799097#u32 1329487598#u32 522665344#u32 1041667360#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2040799097#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1329487598#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 522665344#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2040799097#u32) (JFs_TX2_RawMath.extend 1329487598#u32) (JFs_TX2_RawMath.extend 522665344#u32) (JFs_TX2_RawMath.extend 1041667360#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1041667360#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails19.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails19.value1_3=
      ok (.Ok (pack 2040799097#u32 1329487598#u32 522665344#u32 1041667360#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2040799097<2147483647 ∧ 1329487598<2147483647) ∧ (522665344<2147483647 ∧ 1041667360<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2040799097#u32 1329487598#u32 522665344#u32 1041667360#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3277691812#u64 2112828276#u64 6777176762#u64 6395788079#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2040799097#u32 1329487598#u32 522665344#u32 1041667360#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1251449952#u64 864480817#u64 3389075130#u64 4680503633#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q9_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7074832398#u64 4724150306#u64 13054141283#u64 9622465381#u64⟩,⟨pack 3943839558#u64 3299558946#u64 8868906247#u64 6790062129#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10142007182#u64 6953660895#u64 19008950981#u64 11894194509#u64⟩,⟨pack 7693087145#u64 5108196579#u64 14600851176#u64 10066149948#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4738396593278749263#u64 672408631395344785#u64 10025220918813242564#u64 2003298111846190047#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 768797460#u32 471272793#u32 1468287654#u32 410772689#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 768797460#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 471272793#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1468287654#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 410772689#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5105411960233842722#u64 2257223634435642594#u64 11843573220327089073#u64 5851249112868815337#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 768797460#u32 471272793#u32 1468287654#u32 410772689#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 768797460#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 471272793#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1468287654#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 768797460#u32) (JFs_TX2_RawMath.extend 471272793#u32) (JFs_TX2_RawMath.extend 1468287654#u32) (JFs_TX2_RawMath.extend 410772689#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 410772689#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails19.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails19.value2_3=
      ok (.Ok (pack 768797460#u32 471272793#u32 1468287654#u32 410772689#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (768797460<2147483647 ∧ 471272793<2147483647) ∧ (1468287654<2147483647 ∧ 410772689<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 768797460#u32 471272793#u32 1468287654#u32 410772689#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7074832398#u64 4724150306#u64 13054141283#u64 9622465381#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 768797460#u32 471272793#u32 1468287654#u32 410772689#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3943839558#u64 3299558946#u64 8868906247#u64 6790062129#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q9_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1552072594#u32,511209954#u32⟩,⟨1829081805#u32,1156776274#u32⟩⟩,⟨⟨1250636204#u32,813229285#u32⟩,⟨1715949294#u32,1476215360#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q9_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q9_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10142007182%2147483647 at h0
  norm_num at h0
  have e0 : a0=1552072594#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6953660895%2147483647 at h1
  norm_num at h1
  have e1 : a1=511209954#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19008950981%2147483647 at h2
  norm_num at h2
  have e2 : a2=1829081805#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11894194509%2147483647 at h3
  norm_num at h3
  have e3 : a3=1156776274#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7693087145%2147483647 at h4
  norm_num at h4
  have e4 : a4=1250636204#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5108196579%2147483647 at h5
  norm_num at h5
  have e5 : a5=813229285#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14600851176%2147483647 at h6
  norm_num at h6
  have e6 : a6=1715949294#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10066149948%2147483647 at h7
  norm_num at h7
  have e7 : a7=1476215360#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 9)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q9_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 9))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails19.value0_3
      from JFr_TX2_Tails19.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 9))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails19.value1_3
      from JFr_TX2_Tails19.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 9))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails19.value2_3
      from JFr_TX2_Tails19.source2_3,
    JFz_TX2_Q9_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q9_Raw30.after=JFz_TX2_Q9_Raw31.before := rfl
  have same2 : JFz_TX2_Q9_Raw31.after=JFz_TX2_Q9_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q9_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q9_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q9_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1378825718#u32,1683014341#u32⟩,⟨1419725700#u32,1904933936#u32⟩⟩,⟨⟨1033953609#u32,982533070#u32⟩,⟨210015257#u32,31619076#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1378825718<2147483647 ∧ 1683014341<2147483647) ∧ (1419725700<2147483647 ∧ 1904933936<2147483647)) ∧
    ((1033953609<2147483647 ∧ 982533070<2147483647) ∧ (210015257<2147483647 ∧ 31619076<2147483647))
  omega
theorem addition : decode JFz_TX2_Q9_Head3.value+decode JFz_TX2_Q9_Tail3.value=decode value := by
  change (⟨⟨⟨1974236771,1171804387⟩,⟨1738127542,748157662⟩⟩,⟨⟨1930801052,169303785⟩,⟨641549610,702887363⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1552072594,511209954⟩,⟨1829081805,1156776274⟩⟩,⟨⟨1250636204,813229285⟩,⟨1715949294,1476215360⟩⟩⟩=⟨⟨⟨1378825718,1683014341⟩,⟨1419725700,1904933936⟩⟩,⟨⟨1033953609,982533070⟩,⟨210015257,31619076⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 9)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 9 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q9_Head3.value JFz_TX2_Q9_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q9_Head3.source,
      JFz_TX2_Q9_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q9_Head3.value := by
    change ((1974236771<2147483647 ∧ 1171804387<2147483647) ∧ (1738127542<2147483647 ∧ 748157662<2147483647)) ∧
      ((1930801052<2147483647 ∧ 169303785<2147483647) ∧ (641549610<2147483647 ∧ 702887363<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q9_Tail3.value := by
    change ((1552072594<2147483647 ∧ 511209954<2147483647) ∧ (1829081805<2147483647 ∧ 1156776274<2147483647)) ∧
      ((1250636204<2147483647 ∧ 813229285<2147483647) ∧ (1715949294<2147483647 ∧ 1476215360<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q9_Dot3
end
