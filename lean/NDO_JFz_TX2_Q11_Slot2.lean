import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails21
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1046004422#u32,1685641642#u32⟩,⟨417963989#u32,2089703599#u32⟩⟩,⟨⟨982326422#u32,1047718940#u32⟩,⟨1872258972#u32,739702374#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 11 2 0 0 26%2147483647=1046004422 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*520915304+855639275*1768992786+867568255*2075644729+352063*1881981705+1106523000*2097958790+1554033304*2077667999+1430280692*1624034984+1491718280*944767960+118514350*585090284+1675652887*284782149+1364884909*1372058662+1135303194*1554961198+304762092*1371194223+1465393816*1014216838+824208172*475336845+1752653420*457350078+1385409049*2084437676+1003904973*514502485+1298953245*892510528+2005758375*1165143763+497936241*501243922+235809508*1580835089+1478307182*1859251007+1858903615*2124681520+628035096*1560973222+1244951250*1633445578)%2147483647=1046004422
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 11 2 1 0 26%2147483647=1685641642 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+1483149559*1768992786+655227887*2075644729+39062738*1881981705+729079828*2097958790+67370206*2077667999+1685049618*1624034984+385547620*944767960+1786803209*585090284+779721715*284782149+594709522*1372058662+338788461*1554961198+526756808*1371194223+184076238*1014216838+1852498770*475336845+2102463508*457350078+1086671526*2084437676+1147694576*514502485+1504805752*892510528+2005073905*1165143763+185008025*501243922+1485990146*1580835089+1255280192*1859251007+1018329259*2124681520+570157693*1560973222+1511904630*1633445578)%2147483647=1685641642
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 11 2 2 0 26%2147483647=417963989 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+1898717401*1768992786+1032732628*2075644729+1313565596*1881981705+1074182998*2097958790+1410213748*2077667999+1182702806*1624034984+321711020*944767960+2062791928*585090284+1188803754*284782149+2038502201*1372058662+735931834*1554961198+1330533011*1371194223+1052874750*1014216838+950153811*475336845+1225424092*457350078+1659116453*2084437676+1474177753*514502485+2073609211*892510528+1602919019*1165143763+1865917845*501243922+1085624123*1580835089+1837870964*1859251007+1550509101*2124681520+1661725734*1560973222+2066655336*1633445578)%2147483647=417963989
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 11 2 3 0 26%2147483647=2089703599 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+1849775942*1768992786+656039795*2075644729+1840648083*1881981705+246996287*2097958790+1369248953*2077667999+1132591724*1624034984+92744917*944767960+1719480363*585090284+1266677922*284782149+377386917*1372058662+735227219*1554961198+465096431*1371194223+451889791*1014216838+1379836302*475336845+618598847*457350078+1624084534*2084437676+1511477847*514502485+1840812326*892510528+185546252*1165143763+2145463598*501243922+82870699*1580835089+1625323762*1859251007+1843639311*2124681520+1777269271*1560973222+1645120956*1633445578)%2147483647=2089703599
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 11 2 4 0 26%2147483647=982326422 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+1112406525*1768992786+1345999435*2075644729+752376469*1881981705+634588140*2097958790+1419170319*2077667999+1702860885*1624034984+710076517*944767960+1256487405*585090284+1114745059*284782149+1137838899*1372058662+1254184109*1554961198+1038210451*1371194223+274378589*1014216838+171986381*475336845+1536678585*457350078+1305878831*2084437676+1335902916*514502485+1755193245*892510528+2023391453*1165143763+293456010*501243922+1751078325*1580835089+1423042536*1859251007+1749638204*2124681520+1345811362*1560973222+1284924881*1633445578)%2147483647=982326422
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 11 2 5 0 26%2147483647=1047718940 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+1796814865*1768992786+1253123171*2075644729+1317611639*1881981705+1559245386*2097958790+1866942376*2077667999+1973593402*1624034984+47019780*944767960+1353487525*585090284+1840161555*284782149+2003659556*1372058662+200559114*1554961198+334988447*1371194223+2023650872*1014216838+1296497964*475336845+34285357*457350078+1685894190*2084437676+995962325*514502485+1295624230*892510528+1199631211*1165143763+1948677857*501243922+1425322328*1580835089+1466877680*1859251007+702011012*2124681520+937706871*1560973222+455802666*1633445578)%2147483647=1047718940
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 11 2 6 0 26%2147483647=1872258972 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+1838939499*1768992786+1353876630*2075644729+1258713036*1881981705+1947503436*2097958790+1271796599*2077667999+1660157177*1624034984+564707688*944767960+1858113864*585090284+1015817431*284782149+1264608004*1372058662+735383960*1554961198+221696734*1371194223+1297524163*1014216838+109088572*475336845+792206628*457350078+1921581249*2084437676+94118806*514502485+476103426*892510528+239612482*1165143763+177052717*501243922+826458039*1580835089+1923715623*1859251007+1014161165*2124681520+1341609618*1560973222+786325583*1633445578)%2147483647=1872258972
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 11 2 7 0 26%2147483647=739702374 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*520915304+418714188*1768992786+1675147475*2075644729+1674326661*1881981705+547797802*2097958790+2073962627*2077667999+897270857*1624034984+1582958967*944767960+49892701*585090284+1256824732*284782149+1435903714*1372058662+742583315*1554961198+1789294768*1371194223+13407412*1014216838+518661610*475336845+1259751297*457350078+1695663205*2084437676+2068940067*514502485+940478841*892510528+1982757556*1165143763+1956713516*501243922+863066484*1580835089+522298462*1859251007+1343575777*2124681520+771712139*1560973222+157728743*1633445578)%2147483647=739702374
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 11 2
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
end AspisR1.JFz_TX2_Q11_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3023277713#u64 1587218481#u64 6346001087#u64 2596786464#u64⟩,⟨pack 3025148361#u64 1445162712#u64 4193634787#u64 3943741792#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4065991546071741192#u64 2180156098300352346#u64 12407397960153853269#u64 5508913480538825185#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 300181499#u32 815969912#u32 2034095948#u32 803373791#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 300181499#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 815969912#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2034095948#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 803373791#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3730521627948295802#u64 738459717149678706#u64 8047111800666955467#u64 5191881413824491546#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 300181499#u32 815969912#u32 2034095948#u32 803373791#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 300181499#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 815969912#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2034095948#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 300181499#u32) (JFs_TX2_RawMath.extend 815969912#u32) (JFs_TX2_RawMath.extend 2034095948#u32) (JFs_TX2_RawMath.extend 803373791#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 803373791#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails21.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value0_2=
      ok (.Ok (pack 300181499#u32 815969912#u32 2034095948#u32 803373791#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (300181499<2147483647 ∧ 815969912<2147483647) ∧ (2034095948<2147483647 ∧ 803373791<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 300181499#u32 815969912#u32 2034095948#u32 803373791#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 300181499#u32 815969912#u32 2034095948#u32 803373791#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q11_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3023277713#u64 1587218481#u64 6346001087#u64 2596786464#u64⟩,⟨pack 3025148361#u64 1445162712#u64 4193634787#u64 3943741792#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8597939253#u64 3775961140#u64 12656955527#u64 6419127778#u64⟩,⟨pack 6936668257#u64 3110307220#u64 9001664044#u64 6257475283#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7491696991049015348#u64 738263571031908967#u64 11852750533073742377#u64 4155081029100547174#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1528894085#u32 93578262#u32 425956984#u32 973875503#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1528894085#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 93578262#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 425956984#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 973875503#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5575048519970452586#u64 426826732434574703#u64 9914219955411742526#u64 1645637074859839757#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1528894085#u32 93578262#u32 425956984#u32 973875503#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1528894085#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 93578262#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 425956984#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1528894085#u32) (JFs_TX2_RawMath.extend 93578262#u32) (JFs_TX2_RawMath.extend 425956984#u32) (JFs_TX2_RawMath.extend 973875503#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 973875503#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails21.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value1_2=
      ok (.Ok (pack 1528894085#u32 93578262#u32 425956984#u32 973875503#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1528894085<2147483647 ∧ 93578262<2147483647) ∧ (425956984<2147483647 ∧ 973875503<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1528894085#u32 93578262#u32 425956984#u32 973875503#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3023277713#u64 1587218481#u64 6346001087#u64 2596786464#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1528894085#u32 93578262#u32 425956984#u32 973875503#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3025148361#u64 1445162712#u64 4193634787#u64 3943741792#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8597939253#u64 3775961140#u64 12656955527#u64 6419127778#u64⟩,⟨pack 6936668257#u64 3110307220#u64 9001664044#u64 6257475283#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11133611076#u64 6133495020#u64 19214580777#u64 10256167514#u64⟩,⟨pack 11334877277#u64 5385997579#u64 14592383328#u64 11887856942#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4642451105765699249#u64 1394226371165850042#u64 9525876736789053131#u64 4101981500203483031#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1388818176#u32 1203712658#u32 2058330364#u32 1771489433#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1388818176#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1203712658#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2058330364#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1771489433#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4852430420101873785#u64 4703086659193460395#u64 10355210484077127952#u64 12049015754451543648#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1388818176#u32 1203712658#u32 2058330364#u32 1771489433#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1388818176#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1203712658#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2058330364#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1388818176#u32) (JFs_TX2_RawMath.extend 1203712658#u32) (JFs_TX2_RawMath.extend 2058330364#u32) (JFs_TX2_RawMath.extend 1771489433#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1771489433#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails21.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value2_2=
      ok (.Ok (pack 1388818176#u32 1203712658#u32 2058330364#u32 1771489433#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1388818176<2147483647 ∧ 1203712658<2147483647) ∧ (2058330364<2147483647 ∧ 1771489433<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1388818176#u32 1203712658#u32 2058330364#u32 1771489433#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8597939253#u64 3775961140#u64 12656955527#u64 6419127778#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1388818176#u32 1203712658#u32 2058330364#u32 1771489433#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6936668257#u64 3110307220#u64 9001664044#u64 6257475283#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨396192841#u32,1838527726#u32⟩,⟨2034711601#u32,1666232926#u32⟩⟩,⟨⟨597459042#u32,1091030285#u32⟩,⟨1707481446#u32,1150438707#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q11_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q11_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11133611076%2147483647 at h0
  norm_num at h0
  have e0 : a0=396192841#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6133495020%2147483647 at h1
  norm_num at h1
  have e1 : a1=1838527726#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19214580777%2147483647 at h2
  norm_num at h2
  have e2 : a2=2034711601#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10256167514%2147483647 at h3
  norm_num at h3
  have e3 : a3=1666232926#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=11334877277%2147483647 at h4
  norm_num at h4
  have e4 : a4=597459042#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5385997579%2147483647 at h5
  norm_num at h5
  have e5 : a5=1091030285#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14592383328%2147483647 at h6
  norm_num at h6
  have e6 : a6=1707481446#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11887856942%2147483647 at h7
  norm_num at h7
  have e7 : a7=1150438707#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q11_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails21.value0_2
      from JFr_TX2_Tails21.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails21.value1_2
      from JFr_TX2_Tails21.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails21.value2_2
      from JFr_TX2_Tails21.source2_2,
    JFz_TX2_Q11_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q11_Raw20.after=JFz_TX2_Q11_Raw21.before := rfl
  have same2 : JFz_TX2_Q11_Raw21.after=JFz_TX2_Q11_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q11_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q11_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q11_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1442197263#u32,1376685721#u32⟩,⟨305191943#u32,1608452878#u32⟩⟩,⟨⟨1579785464#u32,2138749225#u32⟩,⟨1432256771#u32,1890141081#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1442197263<2147483647 ∧ 1376685721<2147483647) ∧ (305191943<2147483647 ∧ 1608452878<2147483647)) ∧
    ((1579785464<2147483647 ∧ 2138749225<2147483647) ∧ (1432256771<2147483647 ∧ 1890141081<2147483647))
  omega
theorem addition : decode JFz_TX2_Q11_Head2.value+decode JFz_TX2_Q11_Tail2.value=decode value := by
  change (⟨⟨⟨1046004422,1685641642⟩,⟨417963989,2089703599⟩⟩,⟨⟨982326422,1047718940⟩,⟨1872258972,739702374⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨396192841,1838527726⟩,⟨2034711601,1666232926⟩⟩,⟨⟨597459042,1091030285⟩,⟨1707481446,1150438707⟩⟩⟩=⟨⟨⟨1442197263,1376685721⟩,⟨305191943,1608452878⟩⟩,⟨⟨1579785464,2138749225⟩,⟨1432256771,1890141081⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 11 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q11_Head2.value JFz_TX2_Q11_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q11_Head2.source,
      JFz_TX2_Q11_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q11_Head2.value := by
    change ((1046004422<2147483647 ∧ 1685641642<2147483647) ∧ (417963989<2147483647 ∧ 2089703599<2147483647)) ∧
      ((982326422<2147483647 ∧ 1047718940<2147483647) ∧ (1872258972<2147483647 ∧ 739702374<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q11_Tail2.value := by
    change ((396192841<2147483647 ∧ 1838527726<2147483647) ∧ (2034711601<2147483647 ∧ 1666232926<2147483647)) ∧
      ((597459042<2147483647 ∧ 1091030285<2147483647) ∧ (1707481446<2147483647 ∧ 1150438707<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q11_Dot2
end
