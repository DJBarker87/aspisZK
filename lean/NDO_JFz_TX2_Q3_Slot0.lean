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
namespace AspisR1.JFz_TX2_Q3_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨834738904#u32,996764480#u32⟩,⟨87245128#u32,292072067#u32⟩⟩,⟨⟨1844701120#u32,1255706535#u32⟩,⟨1375568450#u32,705534715#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 3 0 0 0 26%2147483647=834738904 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*277638934+855639275*647166701+867568255*1925653782+352063*861553329+1106523000*609195270+1554033304*931471452+1430280692*1369776253+1491718280*464064898+118514350*1484778181+1675652887*366050177+1364884909*683619626+1135303194*438607563+304762092*1357042343+1465393816*146268972+824208172*2145650137+1752653420*152560481+1385409049*1742929745+1003904973*1801812346+1298953245*483799625+2005758375*784238672+497936241*370649323+235809508*2070977690+1478307182*188569744+1858903615*1267032915+628035096*677056061+1244951250*1045256294)%2147483647=834738904
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 3 0 1 0 26%2147483647=996764480 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+1483149559*647166701+655227887*1925653782+39062738*861553329+729079828*609195270+67370206*931471452+1685049618*1369776253+385547620*464064898+1786803209*1484778181+779721715*366050177+594709522*683619626+338788461*438607563+526756808*1357042343+184076238*146268972+1852498770*2145650137+2102463508*152560481+1086671526*1742929745+1147694576*1801812346+1504805752*483799625+2005073905*784238672+185008025*370649323+1485990146*2070977690+1255280192*188569744+1018329259*1267032915+570157693*677056061+1511904630*1045256294)%2147483647=996764480
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 3 0 2 0 26%2147483647=87245128 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+1898717401*647166701+1032732628*1925653782+1313565596*861553329+1074182998*609195270+1410213748*931471452+1182702806*1369776253+321711020*464064898+2062791928*1484778181+1188803754*366050177+2038502201*683619626+735931834*438607563+1330533011*1357042343+1052874750*146268972+950153811*2145650137+1225424092*152560481+1659116453*1742929745+1474177753*1801812346+2073609211*483799625+1602919019*784238672+1865917845*370649323+1085624123*2070977690+1837870964*188569744+1550509101*1267032915+1661725734*677056061+2066655336*1045256294)%2147483647=87245128
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 3 0 3 0 26%2147483647=292072067 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+1849775942*647166701+656039795*1925653782+1840648083*861553329+246996287*609195270+1369248953*931471452+1132591724*1369776253+92744917*464064898+1719480363*1484778181+1266677922*366050177+377386917*683619626+735227219*438607563+465096431*1357042343+451889791*146268972+1379836302*2145650137+618598847*152560481+1624084534*1742929745+1511477847*1801812346+1840812326*483799625+185546252*784238672+2145463598*370649323+82870699*2070977690+1625323762*188569744+1843639311*1267032915+1777269271*677056061+1645120956*1045256294)%2147483647=292072067
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 3 0 4 0 26%2147483647=1844701120 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+1112406525*647166701+1345999435*1925653782+752376469*861553329+634588140*609195270+1419170319*931471452+1702860885*1369776253+710076517*464064898+1256487405*1484778181+1114745059*366050177+1137838899*683619626+1254184109*438607563+1038210451*1357042343+274378589*146268972+171986381*2145650137+1536678585*152560481+1305878831*1742929745+1335902916*1801812346+1755193245*483799625+2023391453*784238672+293456010*370649323+1751078325*2070977690+1423042536*188569744+1749638204*1267032915+1345811362*677056061+1284924881*1045256294)%2147483647=1844701120
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 3 0 5 0 26%2147483647=1255706535 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+1796814865*647166701+1253123171*1925653782+1317611639*861553329+1559245386*609195270+1866942376*931471452+1973593402*1369776253+47019780*464064898+1353487525*1484778181+1840161555*366050177+2003659556*683619626+200559114*438607563+334988447*1357042343+2023650872*146268972+1296497964*2145650137+34285357*152560481+1685894190*1742929745+995962325*1801812346+1295624230*483799625+1199631211*784238672+1948677857*370649323+1425322328*2070977690+1466877680*188569744+702011012*1267032915+937706871*677056061+455802666*1045256294)%2147483647=1255706535
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 3 0 6 0 26%2147483647=1375568450 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+1838939499*647166701+1353876630*1925653782+1258713036*861553329+1947503436*609195270+1271796599*931471452+1660157177*1369776253+564707688*464064898+1858113864*1484778181+1015817431*366050177+1264608004*683619626+735383960*438607563+221696734*1357042343+1297524163*146268972+109088572*2145650137+792206628*152560481+1921581249*1742929745+94118806*1801812346+476103426*483799625+239612482*784238672+177052717*370649323+826458039*2070977690+1923715623*188569744+1014161165*1267032915+1341609618*677056061+786325583*1045256294)%2147483647=1375568450
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 3 0 7 0 26%2147483647=705534715 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*277638934+418714188*647166701+1675147475*1925653782+1674326661*861553329+547797802*609195270+2073962627*931471452+897270857*1369776253+1582958967*464064898+49892701*1484778181+1256824732*366050177+1435903714*683619626+742583315*438607563+1789294768*1357042343+13407412*146268972+518661610*2145650137+1259751297*152560481+1695663205*1742929745+2068940067*1801812346+940478841*483799625+1982757556*784238672+1956713516*370649323+863066484*2070977690+522298462*188569744+1343575777*1267032915+771712139*677056061+157728743*1045256294)%2147483647=705534715
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 3 0
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
end AspisR1.JFz_TX2_Q3_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4593718090#u64 2823593143#u64 5929159948#u64 2942092358#u64⟩,⟨pack 3915301028#u64 3217488849#u64 5649733925#u64 4650014910#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 8764557070730700506#u64 3425019161015509800#u64 10709261897786059555#u64 5612385661825211962#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 2073701491#u32 191036810#u32 935107195#u32 1595190767#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2073701491#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 191036810#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 935107195#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1595190767#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5301332313764431191#u64 2665985532311897187#u64 11514865829055696440#u64 6595718930153091559#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 2073701491#u32 191036810#u32 935107195#u32 1595190767#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2073701491#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 191036810#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 935107195#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2073701491#u32) (JFs_TX2_RawMath.extend 191036810#u32) (JFs_TX2_RawMath.extend 935107195#u32) (JFs_TX2_RawMath.extend 1595190767#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1595190767#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails13.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value0_0=
      ok (.Ok (pack 2073701491#u32 191036810#u32 935107195#u32 1595190767#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2073701491<2147483647 ∧ 191036810<2147483647) ∧ (935107195<2147483647 ∧ 1595190767<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 2073701491#u32 191036810#u32 935107195#u32 1595190767#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 2073701491#u32 191036810#u32 935107195#u32 1595190767#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q3_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4593718090#u64 2823593143#u64 5929159948#u64 2942092358#u64⟩,⟨pack 3915301028#u64 3217488849#u64 5649733925#u64 4650014910#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7443235152#u64 4292910944#u64 10296112805#u64 5757153754#u64⟩,⟨pack 6074464292#u64 5195930742#u64 11179794296#u64 6218305233#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4471282361467522762#u64 2584935346640056488#u64 8883154655228185961#u64 5160229726384605795#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 180225135#u32 1321488013#u32 852164804#u32 1378216588#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 180225135#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1321488013#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 852164804#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1378216588#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4411118235584517676#u64 895265211195548343#u64 8771134210634898980#u64 1803450315130531088#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 180225135#u32 1321488013#u32 852164804#u32 1378216588#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 180225135#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1321488013#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 852164804#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 180225135#u32) (JFs_TX2_RawMath.extend 1321488013#u32) (JFs_TX2_RawMath.extend 852164804#u32) (JFs_TX2_RawMath.extend 1378216588#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1378216588#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails13.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value1_0=
      ok (.Ok (pack 180225135#u32 1321488013#u32 852164804#u32 1378216588#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (180225135<2147483647 ∧ 1321488013<2147483647) ∧ (852164804<2147483647 ∧ 1378216588<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 180225135#u32 1321488013#u32 852164804#u32 1378216588#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4593718090#u64 2823593143#u64 5929159948#u64 2942092358#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 180225135#u32 1321488013#u32 852164804#u32 1378216588#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3915301028#u64 3217488849#u64 5649733925#u64 4650014910#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q3_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7443235152#u64 4292910944#u64 10296112805#u64 5757153754#u64⟩,⟨pack 6074464292#u64 5195930742#u64 11179794296#u64 6218305233#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10241941470#u64 6178315004#u64 15951103641#u64 9020619633#u64⟩,⟨pack 10306316320#u64 9109305478#u64 17231078964#u64 12010294303#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5088140684613350545#u64 1424841342094467151#u64 9674495076843840493#u64 3734197969866422030#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1813109462#u32 795545939#u32 1267802821#u32 1962326423#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1813109462#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 795545939#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1267802821#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1962326423#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 6359828545580540737#u64 4762662938145233574#u64 10248488701277200995#u64 10834912866641907101#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1813109462#u32 795545939#u32 1267802821#u32 1962326423#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1813109462#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 795545939#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1267802821#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1813109462#u32) (JFs_TX2_RawMath.extend 795545939#u32) (JFs_TX2_RawMath.extend 1267802821#u32) (JFs_TX2_RawMath.extend 1962326423#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1962326423#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails13.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value2_0=
      ok (.Ok (pack 1813109462#u32 795545939#u32 1267802821#u32 1962326423#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1813109462<2147483647 ∧ 795545939<2147483647) ∧ (1267802821<2147483647 ∧ 1962326423<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1813109462#u32 795545939#u32 1267802821#u32 1962326423#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7443235152#u64 4292910944#u64 10296112805#u64 5757153754#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1813109462#u32 795545939#u32 1267802821#u32 1962326423#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6074464292#u64 5195930742#u64 11179794296#u64 6218305233#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q3_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1652006882#u32,1883347710#u32⟩,⟨918718112#u32,430685045#u32⟩⟩,⟨⟨1716381732#u32,519370890#u32⟩,⟨51209788#u32,1272876068#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q3_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q3_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10241941470%2147483647 at h0
  norm_num at h0
  have e0 : a0=1652006882#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6178315004%2147483647 at h1
  norm_num at h1
  have e1 : a1=1883347710#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15951103641%2147483647 at h2
  norm_num at h2
  have e2 : a2=918718112#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9020619633%2147483647 at h3
  norm_num at h3
  have e3 : a3=430685045#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10306316320%2147483647 at h4
  norm_num at h4
  have e4 : a4=1716381732#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=9109305478%2147483647 at h5
  norm_num at h5
  have e5 : a5=519370890#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17231078964%2147483647 at h6
  norm_num at h6
  have e6 : a6=51209788#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12010294303%2147483647 at h7
  norm_num at h7
  have e7 : a7=1272876068#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q3_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails13.value0_0
      from JFr_TX2_Tails13.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails13.value1_0
      from JFr_TX2_Tails13.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails13.value2_0
      from JFr_TX2_Tails13.source2_0,
    JFz_TX2_Q3_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q3_Raw00.after=JFz_TX2_Q3_Raw01.before := rfl
  have same2 : JFz_TX2_Q3_Raw01.after=JFz_TX2_Q3_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q3_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q3_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q3_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨339262139#u32,732628543#u32⟩,⟨1005963240#u32,722757112#u32⟩⟩,⟨⟨1413599205#u32,1775077425#u32⟩,⟨1426778238#u32,1978410783#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((339262139<2147483647 ∧ 732628543<2147483647) ∧ (1005963240<2147483647 ∧ 722757112<2147483647)) ∧
    ((1413599205<2147483647 ∧ 1775077425<2147483647) ∧ (1426778238<2147483647 ∧ 1978410783<2147483647))
  omega
theorem addition : decode JFz_TX2_Q3_Head0.value+decode JFz_TX2_Q3_Tail0.value=decode value := by
  change (⟨⟨⟨834738904,996764480⟩,⟨87245128,292072067⟩⟩,⟨⟨1844701120,1255706535⟩,⟨1375568450,705534715⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1652006882,1883347710⟩,⟨918718112,430685045⟩⟩,⟨⟨1716381732,519370890⟩,⟨51209788,1272876068⟩⟩⟩=⟨⟨⟨339262139,732628543⟩,⟨1005963240,722757112⟩⟩,⟨⟨1413599205,1775077425⟩,⟨1426778238,1978410783⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 3 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q3_Head0.value JFz_TX2_Q3_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q3_Head0.source,
      JFz_TX2_Q3_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q3_Head0.value := by
    change ((834738904<2147483647 ∧ 996764480<2147483647) ∧ (87245128<2147483647 ∧ 292072067<2147483647)) ∧
      ((1844701120<2147483647 ∧ 1255706535<2147483647) ∧ (1375568450<2147483647 ∧ 705534715<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q3_Tail0.value := by
    change ((1652006882<2147483647 ∧ 1883347710<2147483647) ∧ (918718112<2147483647 ∧ 430685045<2147483647)) ∧
      ((1716381732<2147483647 ∧ 519370890<2147483647) ∧ (51209788<2147483647 ∧ 1272876068<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q3_Dot0
end
