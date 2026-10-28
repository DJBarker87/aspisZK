import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails17
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1001118425#u32,979039271#u32⟩,⟨288676201#u32,2104661158#u32⟩⟩,⟨⟨1262850038#u32,1303418561#u32⟩,⟨123706085#u32,1356364317#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 7 3 0 0 26%2147483647=1001118425 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1949378207+855639275*670498922+867568255*1255969437+352063*302544559+1106523000*998969542+1554033304*357464366+1430280692*307692307+1491718280*1493652677+118514350*1418150182+1675652887*1527354783+1364884909*1124865106+1135303194*45731855+304762092*388792462+1465393816*1746064111+824208172*1294180139+1752653420*2111540928+1385409049*979788146+1003904973*1922559308+1298953245*670880373+2005758375*2108658073+497936241*1033574245+235809508*639511345+1478307182*1542890066+1858903615*1389943452+628035096*1386721331+1244951250*357023838)%2147483647=1001118425
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 7 3 1 0 26%2147483647=979039271 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+1483149559*670498922+655227887*1255969437+39062738*302544559+729079828*998969542+67370206*357464366+1685049618*307692307+385547620*1493652677+1786803209*1418150182+779721715*1527354783+594709522*1124865106+338788461*45731855+526756808*388792462+184076238*1746064111+1852498770*1294180139+2102463508*2111540928+1086671526*979788146+1147694576*1922559308+1504805752*670880373+2005073905*2108658073+185008025*1033574245+1485990146*639511345+1255280192*1542890066+1018329259*1389943452+570157693*1386721331+1511904630*357023838)%2147483647=979039271
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 7 3 2 0 26%2147483647=288676201 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+1898717401*670498922+1032732628*1255969437+1313565596*302544559+1074182998*998969542+1410213748*357464366+1182702806*307692307+321711020*1493652677+2062791928*1418150182+1188803754*1527354783+2038502201*1124865106+735931834*45731855+1330533011*388792462+1052874750*1746064111+950153811*1294180139+1225424092*2111540928+1659116453*979788146+1474177753*1922559308+2073609211*670880373+1602919019*2108658073+1865917845*1033574245+1085624123*639511345+1837870964*1542890066+1550509101*1389943452+1661725734*1386721331+2066655336*357023838)%2147483647=288676201
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 7 3 3 0 26%2147483647=2104661158 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+1849775942*670498922+656039795*1255969437+1840648083*302544559+246996287*998969542+1369248953*357464366+1132591724*307692307+92744917*1493652677+1719480363*1418150182+1266677922*1527354783+377386917*1124865106+735227219*45731855+465096431*388792462+451889791*1746064111+1379836302*1294180139+618598847*2111540928+1624084534*979788146+1511477847*1922559308+1840812326*670880373+185546252*2108658073+2145463598*1033574245+82870699*639511345+1625323762*1542890066+1843639311*1389943452+1777269271*1386721331+1645120956*357023838)%2147483647=2104661158
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 7 3 4 0 26%2147483647=1262850038 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+1112406525*670498922+1345999435*1255969437+752376469*302544559+634588140*998969542+1419170319*357464366+1702860885*307692307+710076517*1493652677+1256487405*1418150182+1114745059*1527354783+1137838899*1124865106+1254184109*45731855+1038210451*388792462+274378589*1746064111+171986381*1294180139+1536678585*2111540928+1305878831*979788146+1335902916*1922559308+1755193245*670880373+2023391453*2108658073+293456010*1033574245+1751078325*639511345+1423042536*1542890066+1749638204*1389943452+1345811362*1386721331+1284924881*357023838)%2147483647=1262850038
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 7 3 5 0 26%2147483647=1303418561 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+1796814865*670498922+1253123171*1255969437+1317611639*302544559+1559245386*998969542+1866942376*357464366+1973593402*307692307+47019780*1493652677+1353487525*1418150182+1840161555*1527354783+2003659556*1124865106+200559114*45731855+334988447*388792462+2023650872*1746064111+1296497964*1294180139+34285357*2111540928+1685894190*979788146+995962325*1922559308+1295624230*670880373+1199631211*2108658073+1948677857*1033574245+1425322328*639511345+1466877680*1542890066+702011012*1389943452+937706871*1386721331+455802666*357023838)%2147483647=1303418561
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 7 3 6 0 26%2147483647=123706085 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+1838939499*670498922+1353876630*1255969437+1258713036*302544559+1947503436*998969542+1271796599*357464366+1660157177*307692307+564707688*1493652677+1858113864*1418150182+1015817431*1527354783+1264608004*1124865106+735383960*45731855+221696734*388792462+1297524163*1746064111+109088572*1294180139+792206628*2111540928+1921581249*979788146+94118806*1922559308+476103426*670880373+239612482*2108658073+177052717*1033574245+826458039*639511345+1923715623*1542890066+1014161165*1389943452+1341609618*1386721331+786325583*357023838)%2147483647=123706085
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 7 3 7 0 26%2147483647=1356364317 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949378207+418714188*670498922+1675147475*1255969437+1674326661*302544559+547797802*998969542+2073962627*357464366+897270857*307692307+1582958967*1493652677+49892701*1418150182+1256824732*1527354783+1435903714*1124865106+742583315*45731855+1789294768*388792462+13407412*1746064111+518661610*1294180139+1259751297*2111540928+1695663205*979788146+2068940067*1922559308+940478841*670880373+1982757556*2108658073+1956713516*1033574245+863066484*639511345+522298462*1542890066+1343575777*1389943452+771712139*1386721331+157728743*357023838)%2147483647=1356364317
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 7 3
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
end AspisR1.JFz_TX2_Q7_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2991458111#u64 4231800495#u64 7588130908#u64 4971454002#u64⟩,⟨pack 2024765224#u64 1291485424#u64 5059112873#u64 5442816258#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4505822409130916872#u64 6566788332837687371#u64 12394373846739082668#u64 7376793743314327692#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1395919300#u32 2122937230#u32 1921973720#u32 1036184212#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1395919300#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2122937230#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1921973720#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1036184212#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2594130200009576400#u64 2686502329303810475#u64 7229808355452194528#u64 10125568448258919244#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1395919300#u32 2122937230#u32 1921973720#u32 1036184212#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1395919300#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2122937230#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1921973720#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1395919300#u32) (JFs_TX2_RawMath.extend 2122937230#u32) (JFs_TX2_RawMath.extend 1921973720#u32) (JFs_TX2_RawMath.extend 1036184212#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1036184212#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails17.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value0_3=
      ok (.Ok (pack 1395919300#u32 2122937230#u32 1921973720#u32 1036184212#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1395919300<2147483647 ∧ 2122937230<2147483647) ∧ (1921973720<2147483647 ∧ 1036184212<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1395919300#u32 2122937230#u32 1921973720#u32 1036184212#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1395919300#u32 2122937230#u32 1921973720#u32 1036184212#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q7_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2991458111#u64 4231800495#u64 7588130908#u64 4971454002#u64⟩,⟨pack 2024765224#u64 1291485424#u64 5059112873#u64 5442816258#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7372320267#u64 5505369479#u64 13290525165#u64 8931270510#u64⟩,⟨pack 6156232496#u64 2095440652#u64 10444507378#u64 6464720185#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5289590427698977245#u64 721757551244392834#u64 11014545879304278868#u64 4313774867398445687#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 413140317#u32 299277162#u32 1113561769#u32 1529475239#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 413140317#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 299277162#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1113561769#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1529475239#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4806329501474236826#u64 292000170547124453#u64 9593918354812679542#u64 1626507652165270536#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 413140317#u32 299277162#u32 1113561769#u32 1529475239#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 413140317#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 299277162#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1113561769#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 413140317#u32) (JFs_TX2_RawMath.extend 299277162#u32) (JFs_TX2_RawMath.extend 1113561769#u32) (JFs_TX2_RawMath.extend 1529475239#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1529475239#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails17.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value1_3=
      ok (.Ok (pack 413140317#u32 299277162#u32 1113561769#u32 1529475239#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (413140317<2147483647 ∧ 299277162<2147483647) ∧ (1113561769<2147483647 ∧ 1529475239<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 413140317#u32 299277162#u32 1113561769#u32 1529475239#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2991458111#u64 4231800495#u64 7588130908#u64 4971454002#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 413140317#u32 299277162#u32 1113561769#u32 1529475239#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2024765224#u64 1291485424#u64 5059112873#u64 5442816258#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7372320267#u64 5505369479#u64 13290525165#u64 8931270510#u64⟩,⟨pack 6156232496#u64 2095440652#u64 10444507378#u64 6464720185#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10255387876#u64 6904515846#u64 18860671890#u64 12273491813#u64⟩,⟨pack 10054149023#u64 6063206909#u64 15583203347#u64 12932309594#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5023599642087607381#u64 1825324488900448664#u64 9329729064850553687#u64 3940612201866757153#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2147106483#u32 1212965857#u32 612749778#u32 1918010312#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2147106483#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1212965857#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 612749778#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1918010312#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 6181298516602959855#u64 6120801333946377773#u64 9114446433705016742#u64 11044569397966615150#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2147106483#u32 1212965857#u32 612749778#u32 1918010312#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2147106483#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1212965857#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 612749778#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2147106483#u32) (JFs_TX2_RawMath.extend 1212965857#u32) (JFs_TX2_RawMath.extend 612749778#u32) (JFs_TX2_RawMath.extend 1918010312#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1918010312#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails17.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value2_3=
      ok (.Ok (pack 2147106483#u32 1212965857#u32 612749778#u32 1918010312#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2147106483<2147483647 ∧ 1212965857<2147483647) ∧ (612749778<2147483647 ∧ 1918010312<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2147106483#u32 1212965857#u32 612749778#u32 1918010312#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7372320267#u64 5505369479#u64 13290525165#u64 8931270510#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2147106483#u32 1212965857#u32 612749778#u32 1918010312#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6156232496#u64 2095440652#u64 10444507378#u64 6464720185#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1665453288#u32,462064905#u32⟩,⟨1680802714#u32,1536073578#u32⟩⟩,⟨⟨1464214435#u32,1768239615#u32⟩,⟨550817818#u32,47407712#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q7_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q7_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10255387876%2147483647 at h0
  norm_num at h0
  have e0 : a0=1665453288#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6904515846%2147483647 at h1
  norm_num at h1
  have e1 : a1=462064905#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18860671890%2147483647 at h2
  norm_num at h2
  have e2 : a2=1680802714#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=12273491813%2147483647 at h3
  norm_num at h3
  have e3 : a3=1536073578#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10054149023%2147483647 at h4
  norm_num at h4
  have e4 : a4=1464214435#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6063206909%2147483647 at h5
  norm_num at h5
  have e5 : a5=1768239615#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15583203347%2147483647 at h6
  norm_num at h6
  have e6 : a6=550817818#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12932309594%2147483647 at h7
  norm_num at h7
  have e7 : a7=47407712#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q7_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails17.value0_3
      from JFr_TX2_Tails17.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails17.value1_3
      from JFr_TX2_Tails17.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails17.value2_3
      from JFr_TX2_Tails17.source2_3,
    JFz_TX2_Q7_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q7_Raw30.after=JFz_TX2_Q7_Raw31.before := rfl
  have same2 : JFz_TX2_Q7_Raw31.after=JFz_TX2_Q7_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q7_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q7_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q7_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨519088066#u32,1441104176#u32⟩,⟨1969478915#u32,1493251089#u32⟩⟩,⟨⟨579580826#u32,924174529#u32⟩,⟨674523903#u32,1403772029#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((519088066<2147483647 ∧ 1441104176<2147483647) ∧ (1969478915<2147483647 ∧ 1493251089<2147483647)) ∧
    ((579580826<2147483647 ∧ 924174529<2147483647) ∧ (674523903<2147483647 ∧ 1403772029<2147483647))
  omega
theorem addition : decode JFz_TX2_Q7_Head3.value+decode JFz_TX2_Q7_Tail3.value=decode value := by
  change (⟨⟨⟨1001118425,979039271⟩,⟨288676201,2104661158⟩⟩,⟨⟨1262850038,1303418561⟩,⟨123706085,1356364317⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1665453288,462064905⟩,⟨1680802714,1536073578⟩⟩,⟨⟨1464214435,1768239615⟩,⟨550817818,47407712⟩⟩⟩=⟨⟨⟨519088066,1441104176⟩,⟨1969478915,1493251089⟩⟩,⟨⟨579580826,924174529⟩,⟨674523903,1403772029⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 7 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q7_Head3.value JFz_TX2_Q7_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q7_Head3.source,
      JFz_TX2_Q7_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q7_Head3.value := by
    change ((1001118425<2147483647 ∧ 979039271<2147483647) ∧ (288676201<2147483647 ∧ 2104661158<2147483647)) ∧
      ((1262850038<2147483647 ∧ 1303418561<2147483647) ∧ (123706085<2147483647 ∧ 1356364317<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q7_Tail3.value := by
    change ((1665453288<2147483647 ∧ 462064905<2147483647) ∧ (1680802714<2147483647 ∧ 1536073578<2147483647)) ∧
      ((1464214435<2147483647 ∧ 1768239615<2147483647) ∧ (550817818<2147483647 ∧ 47407712<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q7_Dot3
end
