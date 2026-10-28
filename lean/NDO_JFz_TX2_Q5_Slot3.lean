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
namespace AspisR1.JFz_TX2_Q5_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1127816981#u32,1874718308#u32⟩,⟨565655480#u32,2658307#u32⟩⟩,⟨⟨1740528315#u32,174127485#u32⟩,⟨1249741146#u32,993143840#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 5 3 0 0 26%2147483647=1127816981 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1779869961+855639275*993274066+867568255*261647174+352063*2012345872+1106523000*659220362+1554033304*1994098492+1430280692*144661426+1491718280*1915986875+118514350*1564458825+1675652887*249596710+1364884909*1266827446+1135303194*313802706+304762092*1195696930+1465393816*2105210702+824208172*490641156+1752653420*1021964012+1385409049*786336752+1003904973*829009729+1298953245*1357058365+2005758375*282608444+497936241*1853135892+235809508*1675282453+1478307182*1538058994+1858903615*1551216216+628035096*1082029699+1244951250*401089345)%2147483647=1127816981
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 5 3 1 0 26%2147483647=1874718308 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+1483149559*993274066+655227887*261647174+39062738*2012345872+729079828*659220362+67370206*1994098492+1685049618*144661426+385547620*1915986875+1786803209*1564458825+779721715*249596710+594709522*1266827446+338788461*313802706+526756808*1195696930+184076238*2105210702+1852498770*490641156+2102463508*1021964012+1086671526*786336752+1147694576*829009729+1504805752*1357058365+2005073905*282608444+185008025*1853135892+1485990146*1675282453+1255280192*1538058994+1018329259*1551216216+570157693*1082029699+1511904630*401089345)%2147483647=1874718308
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 5 3 2 0 26%2147483647=565655480 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+1898717401*993274066+1032732628*261647174+1313565596*2012345872+1074182998*659220362+1410213748*1994098492+1182702806*144661426+321711020*1915986875+2062791928*1564458825+1188803754*249596710+2038502201*1266827446+735931834*313802706+1330533011*1195696930+1052874750*2105210702+950153811*490641156+1225424092*1021964012+1659116453*786336752+1474177753*829009729+2073609211*1357058365+1602919019*282608444+1865917845*1853135892+1085624123*1675282453+1837870964*1538058994+1550509101*1551216216+1661725734*1082029699+2066655336*401089345)%2147483647=565655480
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 5 3 3 0 26%2147483647=2658307 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+1849775942*993274066+656039795*261647174+1840648083*2012345872+246996287*659220362+1369248953*1994098492+1132591724*144661426+92744917*1915986875+1719480363*1564458825+1266677922*249596710+377386917*1266827446+735227219*313802706+465096431*1195696930+451889791*2105210702+1379836302*490641156+618598847*1021964012+1624084534*786336752+1511477847*829009729+1840812326*1357058365+185546252*282608444+2145463598*1853135892+82870699*1675282453+1625323762*1538058994+1843639311*1551216216+1777269271*1082029699+1645120956*401089345)%2147483647=2658307
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 5 3 4 0 26%2147483647=1740528315 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+1112406525*993274066+1345999435*261647174+752376469*2012345872+634588140*659220362+1419170319*1994098492+1702860885*144661426+710076517*1915986875+1256487405*1564458825+1114745059*249596710+1137838899*1266827446+1254184109*313802706+1038210451*1195696930+274378589*2105210702+171986381*490641156+1536678585*1021964012+1305878831*786336752+1335902916*829009729+1755193245*1357058365+2023391453*282608444+293456010*1853135892+1751078325*1675282453+1423042536*1538058994+1749638204*1551216216+1345811362*1082029699+1284924881*401089345)%2147483647=1740528315
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 5 3 5 0 26%2147483647=174127485 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+1796814865*993274066+1253123171*261647174+1317611639*2012345872+1559245386*659220362+1866942376*1994098492+1973593402*144661426+47019780*1915986875+1353487525*1564458825+1840161555*249596710+2003659556*1266827446+200559114*313802706+334988447*1195696930+2023650872*2105210702+1296497964*490641156+34285357*1021964012+1685894190*786336752+995962325*829009729+1295624230*1357058365+1199631211*282608444+1948677857*1853135892+1425322328*1675282453+1466877680*1538058994+702011012*1551216216+937706871*1082029699+455802666*401089345)%2147483647=174127485
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 5 3 6 0 26%2147483647=1249741146 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+1838939499*993274066+1353876630*261647174+1258713036*2012345872+1947503436*659220362+1271796599*1994098492+1660157177*144661426+564707688*1915986875+1858113864*1564458825+1015817431*249596710+1264608004*1266827446+735383960*313802706+221696734*1195696930+1297524163*2105210702+109088572*490641156+792206628*1021964012+1921581249*786336752+94118806*829009729+476103426*1357058365+239612482*282608444+177052717*1853135892+826458039*1675282453+1923715623*1538058994+1014161165*1551216216+1341609618*1082029699+786325583*401089345)%2147483647=1249741146
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 5 3 7 0 26%2147483647=993143840 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1779869961+418714188*993274066+1675147475*261647174+1674326661*2012345872+547797802*659220362+2073962627*1994098492+897270857*144661426+1582958967*1915986875+49892701*1564458825+1256824732*249596710+1435903714*1266827446+742583315*313802706+1789294768*1195696930+13407412*2105210702+518661610*490641156+1259751297*1021964012+1695663205*786336752+2068940067*829009729+940478841*1357058365+1982757556*282608444+1956713516*1853135892+863066484*1675282453+522298462*1538058994+1343575777*1551216216+771712139*1082029699+157728743*401089345)%2147483647=993143840
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 5 3
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
end AspisR1.JFz_TX2_Q5_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2372421642#u64 1980231381#u64 5297955864#u64 3147185162#u64⟩,⟨pack 1635053382#u64 689946671#u64 4283313302#u64 2190094883#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 3648310378420861471#u64 3080885848485719071#u64 8554846301791358291#u64 3488855316064398641#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 362731764#u32 1194940575#u32 304683535#u32 866011586#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 362731764#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1194940575#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 304683535#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 866011586#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3286896535672594766#u64 985777144502379009#u64 6533489868070645696#u64 3976247527173079557#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 362731764#u32 1194940575#u32 304683535#u32 866011586#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 362731764#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1194940575#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 304683535#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 362731764#u32) (JFs_TX2_RawMath.extend 1194940575#u32) (JFs_TX2_RawMath.extend 304683535#u32) (JFs_TX2_RawMath.extend 866011586#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 866011586#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails15.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value0_3=
      ok (.Ok (pack 362731764#u32 1194940575#u32 304683535#u32 866011586#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (362731764<2147483647 ∧ 1194940575<2147483647) ∧ (304683535<2147483647 ∧ 866011586<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 362731764#u32 1194940575#u32 304683535#u32 866011586#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 362731764#u32 1194940575#u32 304683535#u32 866011586#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q5_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2372421642#u64 1980231381#u64 5297955864#u64 3147185162#u64⟩,⟨pack 1635053382#u64 689946671#u64 4283313302#u64 2190094883#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5949205219#u64 3055639856#u64 12774065312#u64 5729100909#u64⟩,⟨pack 4808239513#u64 2036536617#u64 10853961505#u64 3566343272#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6240893251217861672#u64 2081582870359631148#u64 12987506890750727967#u64 5115871087043179799#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1026627486#u32 894807856#u32 1953018198#u32 898199669#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1026627486#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 894807856#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1953018198#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 898199669#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5059137153103537524#u64 823042421379777417#u64 10228730789239759265#u64 2044682225362373368#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1026627486#u32 894807856#u32 1953018198#u32 898199669#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1026627486#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 894807856#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1953018198#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1026627486#u32) (JFs_TX2_RawMath.extend 894807856#u32) (JFs_TX2_RawMath.extend 1953018198#u32) (JFs_TX2_RawMath.extend 898199669#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 898199669#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails15.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value1_3=
      ok (.Ok (pack 1026627486#u32 894807856#u32 1953018198#u32 898199669#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1026627486<2147483647 ∧ 894807856<2147483647) ∧ (1953018198<2147483647 ∧ 898199669<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1026627486#u32 894807856#u32 1953018198#u32 898199669#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2372421642#u64 1980231381#u64 5297955864#u64 3147185162#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1026627486#u32 894807856#u32 1953018198#u32 898199669#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1635053382#u64 689946671#u64 4283313302#u64 2190094883#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5949205219#u64 3055639856#u64 12774065312#u64 5729100909#u64⟩,⟨pack 4808239513#u64 2036536617#u64 10853961505#u64 3566343272#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10136536545#u64 3993304591#u64 17753691859#u64 8833199928#u64⟩,⟨pack 7760247045#u64 3714965020#u64 16053082008#u64 7872109178#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4591726341084376432#u64 414129047449440390#u64 9224176364654517027#u64 2063122024921918898#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 386773783#u32 385957316#u32 1391145879#u32 1315143470#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 386773783#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 385957316#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1391145879#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1315143470#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4584976942627935987#u64 1399821647718937653#u64 9378925406571397769#u64 6433639637366014911#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 386773783#u32 385957316#u32 1391145879#u32 1315143470#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 386773783#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 385957316#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1391145879#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 386773783#u32) (JFs_TX2_RawMath.extend 385957316#u32) (JFs_TX2_RawMath.extend 1391145879#u32) (JFs_TX2_RawMath.extend 1315143470#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1315143470#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails15.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value2_3=
      ok (.Ok (pack 386773783#u32 385957316#u32 1391145879#u32 1315143470#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (386773783<2147483647 ∧ 385957316<2147483647) ∧ (1391145879<2147483647 ∧ 1315143470<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 386773783#u32 385957316#u32 1391145879#u32 1315143470#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5949205219#u64 3055639856#u64 12774065312#u64 5729100909#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 386773783#u32 385957316#u32 1391145879#u32 1315143470#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4808239513#u64 2036536617#u64 10853961505#u64 3566343272#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1546601957#u32,1845820944#u32⟩,⟨573822683#u32,243265340#u32⟩⟩,⟨⟨1317796104#u32,1567481373#u32⟩,⟨1020696479#u32,1429658237#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q5_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q5_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10136536545%2147483647 at h0
  norm_num at h0
  have e0 : a0=1546601957#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=3993304591%2147483647 at h1
  norm_num at h1
  have e1 : a1=1845820944#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17753691859%2147483647 at h2
  norm_num at h2
  have e2 : a2=573822683#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8833199928%2147483647 at h3
  norm_num at h3
  have e3 : a3=243265340#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7760247045%2147483647 at h4
  norm_num at h4
  have e4 : a4=1317796104#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=3714965020%2147483647 at h5
  norm_num at h5
  have e5 : a5=1567481373#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16053082008%2147483647 at h6
  norm_num at h6
  have e6 : a6=1020696479#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=7872109178%2147483647 at h7
  norm_num at h7
  have e7 : a7=1429658237#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q5_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails15.value0_3
      from JFr_TX2_Tails15.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails15.value1_3
      from JFr_TX2_Tails15.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails15.value2_3
      from JFr_TX2_Tails15.source2_3,
    JFz_TX2_Q5_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q5_Raw30.after=JFz_TX2_Q5_Raw31.before := rfl
  have same2 : JFz_TX2_Q5_Raw31.after=JFz_TX2_Q5_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q5_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q5_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q5_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨526935291#u32,1573055605#u32⟩,⟨1139478163#u32,245923647#u32⟩⟩,⟨⟨910840772#u32,1741608858#u32⟩,⟨122953978#u32,275318430#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((526935291<2147483647 ∧ 1573055605<2147483647) ∧ (1139478163<2147483647 ∧ 245923647<2147483647)) ∧
    ((910840772<2147483647 ∧ 1741608858<2147483647) ∧ (122953978<2147483647 ∧ 275318430<2147483647))
  omega
theorem addition : decode JFz_TX2_Q5_Head3.value+decode JFz_TX2_Q5_Tail3.value=decode value := by
  change (⟨⟨⟨1127816981,1874718308⟩,⟨565655480,2658307⟩⟩,⟨⟨1740528315,174127485⟩,⟨1249741146,993143840⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1546601957,1845820944⟩,⟨573822683,243265340⟩⟩,⟨⟨1317796104,1567481373⟩,⟨1020696479,1429658237⟩⟩⟩=⟨⟨⟨526935291,1573055605⟩,⟨1139478163,245923647⟩⟩,⟨⟨910840772,1741608858⟩,⟨122953978,275318430⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 5 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q5_Head3.value JFz_TX2_Q5_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q5_Head3.source,
      JFz_TX2_Q5_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q5_Head3.value := by
    change ((1127816981<2147483647 ∧ 1874718308<2147483647) ∧ (565655480<2147483647 ∧ 2658307<2147483647)) ∧
      ((1740528315<2147483647 ∧ 174127485<2147483647) ∧ (1249741146<2147483647 ∧ 993143840<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q5_Tail3.value := by
    change ((1546601957<2147483647 ∧ 1845820944<2147483647) ∧ (573822683<2147483647 ∧ 243265340<2147483647)) ∧
      ((1317796104<2147483647 ∧ 1567481373<2147483647) ∧ (1020696479<2147483647 ∧ 1429658237<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q5_Dot3
end
