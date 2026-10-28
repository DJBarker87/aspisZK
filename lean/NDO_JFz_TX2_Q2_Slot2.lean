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
namespace AspisR1.JFz_TX2_Q2_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨414717395#u32,306412008#u32⟩,⟨959923788#u32,1463334089#u32⟩⟩,⟨⟨1814157423#u32,1319139356#u32⟩,⟨1392447430#u32,2077792389#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 2 2 0 0 26%2147483647=414717395 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*206863160+855639275*1822337066+867568255*1335570701+352063*1247974984+1106523000*476152123+1554033304*2041303251+1430280692*616211374+1491718280*1922234322+118514350*2066917255+1675652887*1575231269+1364884909*775139211+1135303194*1735744292+304762092*1997225084+1465393816*1101451832+824208172*1178249039+1752653420*838076126+1385409049*163323941+1003904973*1955169426+1298953245*789723630+2005758375*1097011366+497936241*164365516+235809508*1434225594+1478307182*302633421+1858903615*496442626+628035096*2014452876+1244951250*1889381456)%2147483647=414717395
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 2 2 1 0 26%2147483647=306412008 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+1483149559*1822337066+655227887*1335570701+39062738*1247974984+729079828*476152123+67370206*2041303251+1685049618*616211374+385547620*1922234322+1786803209*2066917255+779721715*1575231269+594709522*775139211+338788461*1735744292+526756808*1997225084+184076238*1101451832+1852498770*1178249039+2102463508*838076126+1086671526*163323941+1147694576*1955169426+1504805752*789723630+2005073905*1097011366+185008025*164365516+1485990146*1434225594+1255280192*302633421+1018329259*496442626+570157693*2014452876+1511904630*1889381456)%2147483647=306412008
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 2 2 2 0 26%2147483647=959923788 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+1898717401*1822337066+1032732628*1335570701+1313565596*1247974984+1074182998*476152123+1410213748*2041303251+1182702806*616211374+321711020*1922234322+2062791928*2066917255+1188803754*1575231269+2038502201*775139211+735931834*1735744292+1330533011*1997225084+1052874750*1101451832+950153811*1178249039+1225424092*838076126+1659116453*163323941+1474177753*1955169426+2073609211*789723630+1602919019*1097011366+1865917845*164365516+1085624123*1434225594+1837870964*302633421+1550509101*496442626+1661725734*2014452876+2066655336*1889381456)%2147483647=959923788
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 2 2 3 0 26%2147483647=1463334089 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+1849775942*1822337066+656039795*1335570701+1840648083*1247974984+246996287*476152123+1369248953*2041303251+1132591724*616211374+92744917*1922234322+1719480363*2066917255+1266677922*1575231269+377386917*775139211+735227219*1735744292+465096431*1997225084+451889791*1101451832+1379836302*1178249039+618598847*838076126+1624084534*163323941+1511477847*1955169426+1840812326*789723630+185546252*1097011366+2145463598*164365516+82870699*1434225594+1625323762*302633421+1843639311*496442626+1777269271*2014452876+1645120956*1889381456)%2147483647=1463334089
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 2 2 4 0 26%2147483647=1814157423 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+1112406525*1822337066+1345999435*1335570701+752376469*1247974984+634588140*476152123+1419170319*2041303251+1702860885*616211374+710076517*1922234322+1256487405*2066917255+1114745059*1575231269+1137838899*775139211+1254184109*1735744292+1038210451*1997225084+274378589*1101451832+171986381*1178249039+1536678585*838076126+1305878831*163323941+1335902916*1955169426+1755193245*789723630+2023391453*1097011366+293456010*164365516+1751078325*1434225594+1423042536*302633421+1749638204*496442626+1345811362*2014452876+1284924881*1889381456)%2147483647=1814157423
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 2 2 5 0 26%2147483647=1319139356 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+1796814865*1822337066+1253123171*1335570701+1317611639*1247974984+1559245386*476152123+1866942376*2041303251+1973593402*616211374+47019780*1922234322+1353487525*2066917255+1840161555*1575231269+2003659556*775139211+200559114*1735744292+334988447*1997225084+2023650872*1101451832+1296497964*1178249039+34285357*838076126+1685894190*163323941+995962325*1955169426+1295624230*789723630+1199631211*1097011366+1948677857*164365516+1425322328*1434225594+1466877680*302633421+702011012*496442626+937706871*2014452876+455802666*1889381456)%2147483647=1319139356
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 2 2 6 0 26%2147483647=1392447430 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+1838939499*1822337066+1353876630*1335570701+1258713036*1247974984+1947503436*476152123+1271796599*2041303251+1660157177*616211374+564707688*1922234322+1858113864*2066917255+1015817431*1575231269+1264608004*775139211+735383960*1735744292+221696734*1997225084+1297524163*1101451832+109088572*1178249039+792206628*838076126+1921581249*163323941+94118806*1955169426+476103426*789723630+239612482*1097011366+177052717*164365516+826458039*1434225594+1923715623*302633421+1014161165*496442626+1341609618*2014452876+786325583*1889381456)%2147483647=1392447430
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 2 2 7 0 26%2147483647=2077792389 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*206863160+418714188*1822337066+1675147475*1335570701+1674326661*1247974984+547797802*476152123+2073962627*2041303251+897270857*616211374+1582958967*1922234322+49892701*2066917255+1256824732*1575231269+1435903714*775139211+742583315*1735744292+1789294768*1997225084+13407412*1101451832+518661610*1178249039+1259751297*838076126+1695663205*163323941+2068940067*1955169426+940478841*789723630+1982757556*1097011366+1956713516*164365516+863066484*1434225594+522298462*302633421+1343575777*496442626+771712139*2014452876+157728743*1889381456)%2147483647=2077792389
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 2 2
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
end AspisR1.JFz_TX2_Q2_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2819272743#u64 2601230721#u64 6748178492#u64 3386840546#u64⟩,⟨pack 2652284988#u64 1180837405#u64 5705241040#u64 3431715828#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5724725120449515986#u64 3483322046876558237#u64 10821700412182903260#u64 3919063526363657948#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1114336599#u32 871536176#u32 883508049#u32 695897146#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1114336599#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 871536176#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 883508049#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 695897146#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4025470661733119938#u64 1776458992215893512#u64 9221698850003809619#u64 5524700030947326244#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1114336599#u32 871536176#u32 883508049#u32 695897146#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1114336599#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 871536176#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 883508049#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1114336599#u32) (JFs_TX2_RawMath.extend 871536176#u32) (JFs_TX2_RawMath.extend 883508049#u32) (JFs_TX2_RawMath.extend 695897146#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 695897146#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails12.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value0_2=
      ok (.Ok (pack 1114336599#u32 871536176#u32 883508049#u32 695897146#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1114336599<2147483647 ∧ 871536176<2147483647) ∧ (883508049<2147483647 ∧ 695897146<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1114336599#u32 871536176#u32 883508049#u32 695897146#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1114336599#u32 871536176#u32 883508049#u32 695897146#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q2_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2819272743#u64 2601230721#u64 6748178492#u64 3386840546#u64⟩,⟨pack 2652284988#u64 1180837405#u64 5705241040#u64 3431715828#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6952702081#u64 6183720232#u64 11372146786#u64 6630775671#u64⟩,⟨pack 5330629129#u64 2979225599#u64 10340466332#u64 4634745370#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4511859882305285898#u64 3946046158220172162#u64 9048129806003688425#u64 6877892355055429701#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 333058467#u32 2006193793#u32 1320674777#u32 1544738539#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 333058467#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2006193793#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1320674777#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1544738539#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4345531323860348511#u64 1373382520666767778#u64 8712806659806967247#u64 2425209287986159655#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 333058467#u32 2006193793#u32 1320674777#u32 1544738539#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 333058467#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2006193793#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1320674777#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 333058467#u32) (JFs_TX2_RawMath.extend 2006193793#u32) (JFs_TX2_RawMath.extend 1320674777#u32) (JFs_TX2_RawMath.extend 1544738539#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1544738539#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails12.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value1_2=
      ok (.Ok (pack 333058467#u32 2006193793#u32 1320674777#u32 1544738539#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (333058467<2147483647 ∧ 2006193793<2147483647) ∧ (1320674777<2147483647 ∧ 1544738539<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 333058467#u32 2006193793#u32 1320674777#u32 1544738539#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2819272743#u64 2601230721#u64 6748178492#u64 3386840546#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 333058467#u32 2006193793#u32 1320674777#u32 1544738539#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2652284988#u64 1180837405#u64 5705241040#u64 3431715828#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6952702081#u64 6183720232#u64 11372146786#u64 6630775671#u64⟩,⟨pack 5330629129#u64 2979225599#u64 10340466332#u64 4634745370#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10098952164#u64 8009936142#u64 17174924381#u64 9331316018#u64⟩,⟨pack 9185436846#u64 5151884991#u64 13842987277#u64 8760022780#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4309528209083002174#u64 1067375139755765717#u64 8230530418528349278#u64 2370794641586485095#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 775011929#u32 1239611142#u32 117111888#u32 1361760304#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 775011929#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1239611142#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 117111888#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1361760304#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3696580383449147930#u64 3632514341064775080#u64 6295487733616351479#u64 6687924301108227443#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 775011929#u32 1239611142#u32 117111888#u32 1361760304#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 775011929#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1239611142#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 117111888#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 775011929#u32) (JFs_TX2_RawMath.extend 1239611142#u32) (JFs_TX2_RawMath.extend 117111888#u32) (JFs_TX2_RawMath.extend 1361760304#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1361760304#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails12.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value2_2=
      ok (.Ok (pack 775011929#u32 1239611142#u32 117111888#u32 1361760304#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (775011929<2147483647 ∧ 1239611142<2147483647) ∧ (117111888<2147483647 ∧ 1361760304<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 775011929#u32 1239611142#u32 117111888#u32 1361760304#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6952702081#u64 6183720232#u64 11372146786#u64 6630775671#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 775011929#u32 1239611142#u32 117111888#u32 1361760304#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5330629129#u64 2979225599#u64 10340466332#u64 4634745370#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1509017576#u32,1567485201#u32⟩,⟨2142538852#u32,741381430#u32⟩⟩,⟨⟨595502258#u32,856917697#u32⟩,⟨958085395#u32,170088192#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q2_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q2_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10098952164%2147483647 at h0
  norm_num at h0
  have e0 : a0=1509017576#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8009936142%2147483647 at h1
  norm_num at h1
  have e1 : a1=1567485201#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17174924381%2147483647 at h2
  norm_num at h2
  have e2 : a2=2142538852#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9331316018%2147483647 at h3
  norm_num at h3
  have e3 : a3=741381430#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9185436846%2147483647 at h4
  norm_num at h4
  have e4 : a4=595502258#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5151884991%2147483647 at h5
  norm_num at h5
  have e5 : a5=856917697#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=13842987277%2147483647 at h6
  norm_num at h6
  have e6 : a6=958085395#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8760022780%2147483647 at h7
  norm_num at h7
  have e7 : a7=170088192#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q2_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails12.value0_2
      from JFr_TX2_Tails12.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails12.value1_2
      from JFr_TX2_Tails12.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails12.value2_2
      from JFr_TX2_Tails12.source2_2,
    JFz_TX2_Q2_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q2_Raw20.after=JFz_TX2_Q2_Raw21.before := rfl
  have same2 : JFz_TX2_Q2_Raw21.after=JFz_TX2_Q2_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q2_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q2_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q2_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1923734971#u32,1873897209#u32⟩,⟨954978993#u32,57231872#u32⟩⟩,⟨⟨262176034#u32,28573406#u32⟩,⟨203049178#u32,100396934#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1923734971<2147483647 ∧ 1873897209<2147483647) ∧ (954978993<2147483647 ∧ 57231872<2147483647)) ∧
    ((262176034<2147483647 ∧ 28573406<2147483647) ∧ (203049178<2147483647 ∧ 100396934<2147483647))
  omega
theorem addition : decode JFz_TX2_Q2_Head2.value+decode JFz_TX2_Q2_Tail2.value=decode value := by
  change (⟨⟨⟨414717395,306412008⟩,⟨959923788,1463334089⟩⟩,⟨⟨1814157423,1319139356⟩,⟨1392447430,2077792389⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1509017576,1567485201⟩,⟨2142538852,741381430⟩⟩,⟨⟨595502258,856917697⟩,⟨958085395,170088192⟩⟩⟩=⟨⟨⟨1923734971,1873897209⟩,⟨954978993,57231872⟩⟩,⟨⟨262176034,28573406⟩,⟨203049178,100396934⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 2 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q2_Head2.value JFz_TX2_Q2_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q2_Head2.source,
      JFz_TX2_Q2_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q2_Head2.value := by
    change ((414717395<2147483647 ∧ 306412008<2147483647) ∧ (959923788<2147483647 ∧ 1463334089<2147483647)) ∧
      ((1814157423<2147483647 ∧ 1319139356<2147483647) ∧ (1392447430<2147483647 ∧ 2077792389<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q2_Tail2.value := by
    change ((1509017576<2147483647 ∧ 1567485201<2147483647) ∧ (2142538852<2147483647 ∧ 741381430<2147483647)) ∧
      ((595502258<2147483647 ∧ 856917697<2147483647) ∧ (958085395<2147483647 ∧ 170088192<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q2_Dot2
end
