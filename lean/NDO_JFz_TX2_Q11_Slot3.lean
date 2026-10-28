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
namespace AspisR1.JFz_TX2_Q11_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨527041227#u32,616592837#u32⟩,⟨1166636224#u32,1575627979#u32⟩⟩,⟨⟨976205306#u32,2115545916#u32⟩,⟨1329936589#u32,671672393#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 11 3 0 0 26%2147483647=527041227 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1949288894+855639275*827297737+867568255*624875378+352063*255723197+1106523000*470307796+1554033304*1433544140+1430280692*1563638950+1491718280*287949322+118514350*471779652+1675652887*504242157+1364884909*1714834037+1135303194*983533914+304762092*548457703+1465393816*763364743+824208172*874758775+1752653420*649299145+1385409049*823256139+1003904973*1180093146+1298953245*1408801200+2005758375*833242455+497936241*259265191+235809508*1165719390+1478307182*2091588721+1858903615*358638064+628035096*560002614+1244951250*1534887870)%2147483647=527041227
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 11 3 1 0 26%2147483647=616592837 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+1483149559*827297737+655227887*624875378+39062738*255723197+729079828*470307796+67370206*1433544140+1685049618*1563638950+385547620*287949322+1786803209*471779652+779721715*504242157+594709522*1714834037+338788461*983533914+526756808*548457703+184076238*763364743+1852498770*874758775+2102463508*649299145+1086671526*823256139+1147694576*1180093146+1504805752*1408801200+2005073905*833242455+185008025*259265191+1485990146*1165719390+1255280192*2091588721+1018329259*358638064+570157693*560002614+1511904630*1534887870)%2147483647=616592837
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 11 3 2 0 26%2147483647=1166636224 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+1898717401*827297737+1032732628*624875378+1313565596*255723197+1074182998*470307796+1410213748*1433544140+1182702806*1563638950+321711020*287949322+2062791928*471779652+1188803754*504242157+2038502201*1714834037+735931834*983533914+1330533011*548457703+1052874750*763364743+950153811*874758775+1225424092*649299145+1659116453*823256139+1474177753*1180093146+2073609211*1408801200+1602919019*833242455+1865917845*259265191+1085624123*1165719390+1837870964*2091588721+1550509101*358638064+1661725734*560002614+2066655336*1534887870)%2147483647=1166636224
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 11 3 3 0 26%2147483647=1575627979 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+1849775942*827297737+656039795*624875378+1840648083*255723197+246996287*470307796+1369248953*1433544140+1132591724*1563638950+92744917*287949322+1719480363*471779652+1266677922*504242157+377386917*1714834037+735227219*983533914+465096431*548457703+451889791*763364743+1379836302*874758775+618598847*649299145+1624084534*823256139+1511477847*1180093146+1840812326*1408801200+185546252*833242455+2145463598*259265191+82870699*1165719390+1625323762*2091588721+1843639311*358638064+1777269271*560002614+1645120956*1534887870)%2147483647=1575627979
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 11 3 4 0 26%2147483647=976205306 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+1112406525*827297737+1345999435*624875378+752376469*255723197+634588140*470307796+1419170319*1433544140+1702860885*1563638950+710076517*287949322+1256487405*471779652+1114745059*504242157+1137838899*1714834037+1254184109*983533914+1038210451*548457703+274378589*763364743+171986381*874758775+1536678585*649299145+1305878831*823256139+1335902916*1180093146+1755193245*1408801200+2023391453*833242455+293456010*259265191+1751078325*1165719390+1423042536*2091588721+1749638204*358638064+1345811362*560002614+1284924881*1534887870)%2147483647=976205306
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 11 3 5 0 26%2147483647=2115545916 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+1796814865*827297737+1253123171*624875378+1317611639*255723197+1559245386*470307796+1866942376*1433544140+1973593402*1563638950+47019780*287949322+1353487525*471779652+1840161555*504242157+2003659556*1714834037+200559114*983533914+334988447*548457703+2023650872*763364743+1296497964*874758775+34285357*649299145+1685894190*823256139+995962325*1180093146+1295624230*1408801200+1199631211*833242455+1948677857*259265191+1425322328*1165719390+1466877680*2091588721+702011012*358638064+937706871*560002614+455802666*1534887870)%2147483647=2115545916
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 11 3 6 0 26%2147483647=1329936589 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+1838939499*827297737+1353876630*624875378+1258713036*255723197+1947503436*470307796+1271796599*1433544140+1660157177*1563638950+564707688*287949322+1858113864*471779652+1015817431*504242157+1264608004*1714834037+735383960*983533914+221696734*548457703+1297524163*763364743+109088572*874758775+792206628*649299145+1921581249*823256139+94118806*1180093146+476103426*1408801200+239612482*833242455+177052717*259265191+826458039*1165719390+1923715623*2091588721+1014161165*358638064+1341609618*560002614+786325583*1534887870)%2147483647=1329936589
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 11 3 7 0 26%2147483647=671672393 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949288894+418714188*827297737+1675147475*624875378+1674326661*255723197+547797802*470307796+2073962627*1433544140+897270857*1563638950+1582958967*287949322+49892701*471779652+1256824732*504242157+1435903714*1714834037+742583315*983533914+1789294768*548457703+13407412*763364743+518661610*874758775+1259751297*649299145+1695663205*823256139+2068940067*1180093146+940478841*1408801200+1982757556*833242455+1956713516*259265191+863066484*1165719390+522298462*2091588721+1343575777*358638064+771712139*560002614+157728743*1534887870)%2147483647=671672393
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 11 3
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
end AspisR1.JFz_TX2_Q11_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5173488073#u64 3794427364#u64 6040209695#u64 3098238361#u64⟩,⟨pack 2428872177#u64 3285630305#u64 5971271587#u64 5437999108#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 6591811053752387413#u64 5263131160838771221#u64 11592385137937313637#u64 3076821919337888546#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1779121831#u32 1251884125#u32 672653367#u32 183997386#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1779121831#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1251884125#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 672653367#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 183997386#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3849455982609276493#u64 2773824644939614143#u64 10335567981967032064#u64 7201160896062813352#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1779121831#u32 1251884125#u32 672653367#u32 183997386#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1779121831#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1251884125#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 672653367#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1779121831#u32) (JFs_TX2_RawMath.extend 1251884125#u32) (JFs_TX2_RawMath.extend 672653367#u32) (JFs_TX2_RawMath.extend 183997386#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 183997386#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails21.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value0_3=
      ok (.Ok (pack 1779121831#u32 1251884125#u32 672653367#u32 183997386#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1779121831<2147483647 ∧ 1251884125<2147483647) ∧ (672653367<2147483647 ∧ 183997386<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1779121831#u32 1251884125#u32 672653367#u32 183997386#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1779121831#u32 1251884125#u32 672653367#u32 183997386#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q11_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5173488073#u64 3794427364#u64 6040209695#u64 3098238361#u64⟩,⟨pack 2428872177#u64 3285630305#u64 5971271587#u64 5437999108#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7819367084#u64 4887895539#u64 10068664275#u64 6764032305#u64⟩,⟨pack 4873570751#u64 4171683508#u64 11094101364#u64 6377097230#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4582893397852913244#u64 2310950895724573918#u64 7807466126726263949#u64 4161496818875522299#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 210062460#u32 1172017524#u32 107159300#u32 1094683005#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 210062460#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1172017524#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 107159300#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1094683005#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4466186049508407989#u64 806042519462793862#u64 8457764331928954399#u64 1390345566149574704#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 210062460#u32 1172017524#u32 107159300#u32 1094683005#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 210062460#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1172017524#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 107159300#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 210062460#u32) (JFs_TX2_RawMath.extend 1172017524#u32) (JFs_TX2_RawMath.extend 107159300#u32) (JFs_TX2_RawMath.extend 1094683005#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1094683005#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails21.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value1_3=
      ok (.Ok (pack 210062460#u32 1172017524#u32 107159300#u32 1094683005#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (210062460<2147483647 ∧ 1172017524<2147483647) ∧ (107159300<2147483647 ∧ 1094683005<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 210062460#u32 1172017524#u32 107159300#u32 1094683005#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5173488073#u64 3794427364#u64 6040209695#u64 3098238361#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 210062460#u32 1172017524#u32 107159300#u32 1094683005#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2428872177#u64 3285630305#u64 5971271587#u64 5437999108#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7819367084#u64 4887895539#u64 10068664275#u64 6764032305#u64⟩,⟨pack 4873570751#u64 4171683508#u64 11094101364#u64 6377097230#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11068275129#u64 6296510271#u64 15031670870#u64 9173306229#u64⟩,⟨pack 8126304851#u64 6775694940#u64 16106599238#u64 10210633477#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4321726633560158234#u64 1338797878110127653#u64 8731542132104896998#u64 2706163498840106890#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1050876361#u32 1467881521#u32 449531974#u32 874683037#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1050876361#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1467881521#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 449531974#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 874683037#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3764406265835753849#u64 4547483840603373245#u64 7954801413760639576#u64 7427834126328475494#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1050876361#u32 1467881521#u32 449531974#u32 874683037#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1050876361#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1467881521#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 449531974#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1050876361#u32) (JFs_TX2_RawMath.extend 1467881521#u32) (JFs_TX2_RawMath.extend 449531974#u32) (JFs_TX2_RawMath.extend 874683037#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 874683037#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails21.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value2_3=
      ok (.Ok (pack 1050876361#u32 1467881521#u32 449531974#u32 874683037#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1050876361<2147483647 ∧ 1467881521<2147483647) ∧ (449531974<2147483647 ∧ 874683037<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1050876361#u32 1467881521#u32 449531974#u32 874683037#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7819367084#u64 4887895539#u64 10068664275#u64 6764032305#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1050876361#u32 1467881521#u32 449531974#u32 874683037#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4873570751#u64 4171683508#u64 11094101364#u64 6377097230#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨330856894#u32,2001542977#u32⟩,⟨2146768988#u32,583371641#u32⟩⟩,⟨⟨1683853910#u32,333243999#u32⟩,⟨1074213709#u32,1620698889#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q11_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q11_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11068275129%2147483647 at h0
  norm_num at h0
  have e0 : a0=330856894#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6296510271%2147483647 at h1
  norm_num at h1
  have e1 : a1=2001542977#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15031670870%2147483647 at h2
  norm_num at h2
  have e2 : a2=2146768988#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9173306229%2147483647 at h3
  norm_num at h3
  have e3 : a3=583371641#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8126304851%2147483647 at h4
  norm_num at h4
  have e4 : a4=1683853910#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6775694940%2147483647 at h5
  norm_num at h5
  have e5 : a5=333243999#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16106599238%2147483647 at h6
  norm_num at h6
  have e6 : a6=1074213709#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10210633477%2147483647 at h7
  norm_num at h7
  have e7 : a7=1620698889#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q11_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails21.value0_3
      from JFr_TX2_Tails21.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails21.value1_3
      from JFr_TX2_Tails21.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails21.value2_3
      from JFr_TX2_Tails21.source2_3,
    JFz_TX2_Q11_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q11_Raw30.after=JFz_TX2_Q11_Raw31.before := rfl
  have same2 : JFz_TX2_Q11_Raw31.after=JFz_TX2_Q11_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q11_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q11_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q11_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨857898121#u32,470652167#u32⟩,⟨1165921565#u32,11515973#u32⟩⟩,⟨⟨512575569#u32,301306268#u32⟩,⟨256666651#u32,144887635#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((857898121<2147483647 ∧ 470652167<2147483647) ∧ (1165921565<2147483647 ∧ 11515973<2147483647)) ∧
    ((512575569<2147483647 ∧ 301306268<2147483647) ∧ (256666651<2147483647 ∧ 144887635<2147483647))
  omega
theorem addition : decode JFz_TX2_Q11_Head3.value+decode JFz_TX2_Q11_Tail3.value=decode value := by
  change (⟨⟨⟨527041227,616592837⟩,⟨1166636224,1575627979⟩⟩,⟨⟨976205306,2115545916⟩,⟨1329936589,671672393⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨330856894,2001542977⟩,⟨2146768988,583371641⟩⟩,⟨⟨1683853910,333243999⟩,⟨1074213709,1620698889⟩⟩⟩=⟨⟨⟨857898121,470652167⟩,⟨1165921565,11515973⟩⟩,⟨⟨512575569,301306268⟩,⟨256666651,144887635⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 11 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q11_Head3.value JFz_TX2_Q11_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q11_Head3.source,
      JFz_TX2_Q11_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q11_Head3.value := by
    change ((527041227<2147483647 ∧ 616592837<2147483647) ∧ (1166636224<2147483647 ∧ 1575627979<2147483647)) ∧
      ((976205306<2147483647 ∧ 2115545916<2147483647) ∧ (1329936589<2147483647 ∧ 671672393<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q11_Tail3.value := by
    change ((330856894<2147483647 ∧ 2001542977<2147483647) ∧ (2146768988<2147483647 ∧ 583371641<2147483647)) ∧
      ((1683853910<2147483647 ∧ 333243999<2147483647) ∧ (1074213709<2147483647 ∧ 1620698889<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q11_Dot3
end
