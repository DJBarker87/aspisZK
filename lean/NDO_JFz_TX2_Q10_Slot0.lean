import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails20
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨53189628#u32,258640848#u32⟩,⟨741498886#u32,1278757754#u32⟩⟩,⟨⟨313964178#u32,147149671#u32⟩,⟨1181211991#u32,771264546#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 10 0 0 0 26%2147483647=53189628 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1052798755+855639275*1162605998+867568255*518458732+352063*1257355432+1106523000*1318137411+1554033304*725681311+1430280692*1710863987+1491718280*443090576+118514350*988017894+1675652887*421059072+1364884909*429090721+1135303194*1143716797+304762092*216274406+1465393816*1858134153+824208172*1474838262+1752653420*248544268+1385409049*568003293+1003904973*997076711+1298953245*1377832947+2005758375*1357662288+497936241*65149396+235809508*614206185+1478307182*1364228434+1858903615*872053513+628035096*2041219489+1244951250*757251895)%2147483647=53189628
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 10 0 1 0 26%2147483647=258640848 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+1483149559*1162605998+655227887*518458732+39062738*1257355432+729079828*1318137411+67370206*725681311+1685049618*1710863987+385547620*443090576+1786803209*988017894+779721715*421059072+594709522*429090721+338788461*1143716797+526756808*216274406+184076238*1858134153+1852498770*1474838262+2102463508*248544268+1086671526*568003293+1147694576*997076711+1504805752*1377832947+2005073905*1357662288+185008025*65149396+1485990146*614206185+1255280192*1364228434+1018329259*872053513+570157693*2041219489+1511904630*757251895)%2147483647=258640848
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 10 0 2 0 26%2147483647=741498886 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+1898717401*1162605998+1032732628*518458732+1313565596*1257355432+1074182998*1318137411+1410213748*725681311+1182702806*1710863987+321711020*443090576+2062791928*988017894+1188803754*421059072+2038502201*429090721+735931834*1143716797+1330533011*216274406+1052874750*1858134153+950153811*1474838262+1225424092*248544268+1659116453*568003293+1474177753*997076711+2073609211*1377832947+1602919019*1357662288+1865917845*65149396+1085624123*614206185+1837870964*1364228434+1550509101*872053513+1661725734*2041219489+2066655336*757251895)%2147483647=741498886
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 10 0 3 0 26%2147483647=1278757754 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+1849775942*1162605998+656039795*518458732+1840648083*1257355432+246996287*1318137411+1369248953*725681311+1132591724*1710863987+92744917*443090576+1719480363*988017894+1266677922*421059072+377386917*429090721+735227219*1143716797+465096431*216274406+451889791*1858134153+1379836302*1474838262+618598847*248544268+1624084534*568003293+1511477847*997076711+1840812326*1377832947+185546252*1357662288+2145463598*65149396+82870699*614206185+1625323762*1364228434+1843639311*872053513+1777269271*2041219489+1645120956*757251895)%2147483647=1278757754
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 10 0 4 0 26%2147483647=313964178 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+1112406525*1162605998+1345999435*518458732+752376469*1257355432+634588140*1318137411+1419170319*725681311+1702860885*1710863987+710076517*443090576+1256487405*988017894+1114745059*421059072+1137838899*429090721+1254184109*1143716797+1038210451*216274406+274378589*1858134153+171986381*1474838262+1536678585*248544268+1305878831*568003293+1335902916*997076711+1755193245*1377832947+2023391453*1357662288+293456010*65149396+1751078325*614206185+1423042536*1364228434+1749638204*872053513+1345811362*2041219489+1284924881*757251895)%2147483647=313964178
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 10 0 5 0 26%2147483647=147149671 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+1796814865*1162605998+1253123171*518458732+1317611639*1257355432+1559245386*1318137411+1866942376*725681311+1973593402*1710863987+47019780*443090576+1353487525*988017894+1840161555*421059072+2003659556*429090721+200559114*1143716797+334988447*216274406+2023650872*1858134153+1296497964*1474838262+34285357*248544268+1685894190*568003293+995962325*997076711+1295624230*1377832947+1199631211*1357662288+1948677857*65149396+1425322328*614206185+1466877680*1364228434+702011012*872053513+937706871*2041219489+455802666*757251895)%2147483647=147149671
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 10 0 6 0 26%2147483647=1181211991 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+1838939499*1162605998+1353876630*518458732+1258713036*1257355432+1947503436*1318137411+1271796599*725681311+1660157177*1710863987+564707688*443090576+1858113864*988017894+1015817431*421059072+1264608004*429090721+735383960*1143716797+221696734*216274406+1297524163*1858134153+109088572*1474838262+792206628*248544268+1921581249*568003293+94118806*997076711+476103426*1377832947+239612482*1357662288+177052717*65149396+826458039*614206185+1923715623*1364228434+1014161165*872053513+1341609618*2041219489+786325583*757251895)%2147483647=1181211991
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 10 0 7 0 26%2147483647=771264546 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1052798755+418714188*1162605998+1675147475*518458732+1674326661*1257355432+547797802*1318137411+2073962627*725681311+897270857*1710863987+1582958967*443090576+49892701*988017894+1256824732*421059072+1435903714*429090721+742583315*1143716797+1789294768*216274406+13407412*1858134153+518661610*1474838262+1259751297*248544268+1695663205*568003293+2068940067*997076711+940478841*1377832947+1982757556*1357662288+1956713516*65149396+863066484*614206185+522298462*1364228434+1343575777*872053513+771712139*2041219489+157728743*757251895)%2147483647=771264546
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 10 0
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
end AspisR1.JFz_TX2_Q10_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4079381550#u64 3627754937#u64 5314441433#u64 2816254591#u64⟩,⟨pack 3812232299#u64 1186126684#u64 5562304686#u64 3473275082#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5513403554647201162#u64 4208203029086605570#u64 8794145970870666884#u64 4082557827423162642#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1204588138#u32 1149344783#u32 212554500#u32 1098306311#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1204588138#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1149344783#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 212554500#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1098306311#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3720121730505178730#u64 2013007915120825163#u64 8026537929444822334#u64 5628306528442151643#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1204588138#u32 1149344783#u32 212554500#u32 1098306311#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1204588138#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1149344783#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 212554500#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1204588138#u32) (JFs_TX2_RawMath.extend 1149344783#u32) (JFs_TX2_RawMath.extend 212554500#u32) (JFs_TX2_RawMath.extend 1098306311#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1098306311#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails20.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value0_0=
      ok (.Ok (pack 1204588138#u32 1149344783#u32 212554500#u32 1098306311#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1204588138<2147483647 ∧ 1149344783<2147483647) ∧ (212554500<2147483647 ∧ 1098306311<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1204588138#u32 1149344783#u32 212554500#u32 1098306311#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1204588138#u32 1149344783#u32 212554500#u32 1098306311#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q10_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4079381550#u64 3627754937#u64 5314441433#u64 2816254591#u64⟩,⟨pack 3812232299#u64 1186126684#u64 5562304686#u64 3473275082#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7008985529#u64 4489694784#u64 11832586543#u64 5928707426#u64⟩,⟨pack 6555008669#u64 3438351173#u64 11727738123#u64 5379620473#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5927430759892207565#u64 1372529749679128437#u64 10612393461576722710#u64 6108091262147733915#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 799110387#u32 566533824#u32 880086924#u32 2039881340#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 799110387#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 566533824#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 880086924#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2039881340#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4991129865298335196#u64 556841335098285933#u64 9345988609030082079#u64 2242816207547816645#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 799110387#u32 566533824#u32 880086924#u32 2039881340#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 799110387#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 566533824#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 880086924#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 799110387#u32) (JFs_TX2_RawMath.extend 566533824#u32) (JFs_TX2_RawMath.extend 880086924#u32) (JFs_TX2_RawMath.extend 2039881340#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2039881340#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails20.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value1_0=
      ok (.Ok (pack 799110387#u32 566533824#u32 880086924#u32 2039881340#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (799110387<2147483647 ∧ 566533824<2147483647) ∧ (880086924<2147483647 ∧ 2039881340<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 799110387#u32 566533824#u32 880086924#u32 2039881340#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4079381550#u64 3627754937#u64 5314441433#u64 2816254591#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 799110387#u32 566533824#u32 880086924#u32 2039881340#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3812232299#u64 1186126684#u64 5562304686#u64 3473275082#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7008985529#u64 4489694784#u64 11832586543#u64 5928707426#u64⟩,⟨pack 6555008669#u64 3438351173#u64 11727738123#u64 5379620473#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9571588225#u64 5395551357#u64 17110776591#u64 7949761713#u64⟩,⟨pack 9950070918#u64 6646097303#u64 13942063899#u64 10823661050#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4094777614711329201#u64 755884776879252439#u64 7644853950351070605#u64 2549472199529709669#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 280778263#u32 1173696087#u32 508481580#u32 2116024614#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 280778263#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1173696087#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 508481580#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2116024614#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2941120463033245429#u64 2602188133214235055#u64 4665686985879075552#u64 7705659275671860976#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 280778263#u32 1173696087#u32 508481580#u32 2116024614#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 280778263#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1173696087#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 508481580#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 280778263#u32) (JFs_TX2_RawMath.extend 1173696087#u32) (JFs_TX2_RawMath.extend 508481580#u32) (JFs_TX2_RawMath.extend 2116024614#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2116024614#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails20.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value2_0=
      ok (.Ok (pack 280778263#u32 1173696087#u32 508481580#u32 2116024614#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (280778263<2147483647 ∧ 1173696087<2147483647) ∧ (508481580<2147483647 ∧ 2116024614<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 280778263#u32 1173696087#u32 508481580#u32 2116024614#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7008985529#u64 4489694784#u64 11832586543#u64 5928707426#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 280778263#u32 1173696087#u32 508481580#u32 2116024614#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6555008669#u64 3438351173#u64 11727738123#u64 5379620473#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨981653637#u32,1100584063#u32⟩,⟨2078391062#u32,1507310772#u32⟩⟩,⟨⟨1360136330#u32,203646362#u32⟩,⟨1057162017#u32,86242815#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q10_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q10_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9571588225%2147483647 at h0
  norm_num at h0
  have e0 : a0=981653637#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5395551357%2147483647 at h1
  norm_num at h1
  have e1 : a1=1100584063#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17110776591%2147483647 at h2
  norm_num at h2
  have e2 : a2=2078391062#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7949761713%2147483647 at h3
  norm_num at h3
  have e3 : a3=1507310772#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9950070918%2147483647 at h4
  norm_num at h4
  have e4 : a4=1360136330#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6646097303%2147483647 at h5
  norm_num at h5
  have e5 : a5=203646362#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=13942063899%2147483647 at h6
  norm_num at h6
  have e6 : a6=1057162017#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10823661050%2147483647 at h7
  norm_num at h7
  have e7 : a7=86242815#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q10_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails20.value0_0
      from JFr_TX2_Tails20.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails20.value1_0
      from JFr_TX2_Tails20.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails20.value2_0
      from JFr_TX2_Tails20.source2_0,
    JFz_TX2_Q10_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q10_Raw00.after=JFz_TX2_Q10_Raw01.before := rfl
  have same2 : JFz_TX2_Q10_Raw01.after=JFz_TX2_Q10_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q10_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q10_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q10_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1034843265#u32,1359224911#u32⟩,⟨672406301#u32,638584879#u32⟩⟩,⟨⟨1674100508#u32,350796033#u32⟩,⟨90890361#u32,857507361#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1034843265<2147483647 ∧ 1359224911<2147483647) ∧ (672406301<2147483647 ∧ 638584879<2147483647)) ∧
    ((1674100508<2147483647 ∧ 350796033<2147483647) ∧ (90890361<2147483647 ∧ 857507361<2147483647))
  omega
theorem addition : decode JFz_TX2_Q10_Head0.value+decode JFz_TX2_Q10_Tail0.value=decode value := by
  change (⟨⟨⟨53189628,258640848⟩,⟨741498886,1278757754⟩⟩,⟨⟨313964178,147149671⟩,⟨1181211991,771264546⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨981653637,1100584063⟩,⟨2078391062,1507310772⟩⟩,⟨⟨1360136330,203646362⟩,⟨1057162017,86242815⟩⟩⟩=⟨⟨⟨1034843265,1359224911⟩,⟨672406301,638584879⟩⟩,⟨⟨1674100508,350796033⟩,⟨90890361,857507361⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 10 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q10_Head0.value JFz_TX2_Q10_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q10_Head0.source,
      JFz_TX2_Q10_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q10_Head0.value := by
    change ((53189628<2147483647 ∧ 258640848<2147483647) ∧ (741498886<2147483647 ∧ 1278757754<2147483647)) ∧
      ((313964178<2147483647 ∧ 147149671<2147483647) ∧ (1181211991<2147483647 ∧ 771264546<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q10_Tail0.value := by
    change ((981653637<2147483647 ∧ 1100584063<2147483647) ∧ (2078391062<2147483647 ∧ 1507310772<2147483647)) ∧
      ((1360136330<2147483647 ∧ 203646362<2147483647) ∧ (1057162017<2147483647 ∧ 86242815<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q10_Dot0
end
