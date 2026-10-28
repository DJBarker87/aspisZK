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
namespace AspisR1.JFz_TX2_Q2_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨188520738#u32,627028879#u32⟩,⟨1672439588#u32,991461882#u32⟩⟩,⟨⟨1719499417#u32,1199346912#u32⟩,⟨1525617945#u32,822708021#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 2 3 0 0 26%2147483647=188520738 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*566056390+855639275*2028950481+867568255*43186015+352063*1475067077+1106523000*1069475621+1554033304*1582524202+1430280692*1151681172+1491718280*720010503+118514350*756841977+1675652887*36180608+1364884909*1544291561+1135303194*1640081406+304762092*316471324+1465393816*1973681341+824208172*1030411537+1752653420*1927816111+1385409049*386386406+1003904973*944062124+1298953245*769004148+2005758375*1412058633+497936241*1248006034+235809508*889698311+1478307182*485251122+1858903615*1079076214+628035096*306760266+1244951250*1714190792)%2147483647=188520738
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 2 3 1 0 26%2147483647=627028879 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+1483149559*2028950481+655227887*43186015+39062738*1475067077+729079828*1069475621+67370206*1582524202+1685049618*1151681172+385547620*720010503+1786803209*756841977+779721715*36180608+594709522*1544291561+338788461*1640081406+526756808*316471324+184076238*1973681341+1852498770*1030411537+2102463508*1927816111+1086671526*386386406+1147694576*944062124+1504805752*769004148+2005073905*1412058633+185008025*1248006034+1485990146*889698311+1255280192*485251122+1018329259*1079076214+570157693*306760266+1511904630*1714190792)%2147483647=627028879
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 2 3 2 0 26%2147483647=1672439588 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+1898717401*2028950481+1032732628*43186015+1313565596*1475067077+1074182998*1069475621+1410213748*1582524202+1182702806*1151681172+321711020*720010503+2062791928*756841977+1188803754*36180608+2038502201*1544291561+735931834*1640081406+1330533011*316471324+1052874750*1973681341+950153811*1030411537+1225424092*1927816111+1659116453*386386406+1474177753*944062124+2073609211*769004148+1602919019*1412058633+1865917845*1248006034+1085624123*889698311+1837870964*485251122+1550509101*1079076214+1661725734*306760266+2066655336*1714190792)%2147483647=1672439588
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 2 3 3 0 26%2147483647=991461882 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+1849775942*2028950481+656039795*43186015+1840648083*1475067077+246996287*1069475621+1369248953*1582524202+1132591724*1151681172+92744917*720010503+1719480363*756841977+1266677922*36180608+377386917*1544291561+735227219*1640081406+465096431*316471324+451889791*1973681341+1379836302*1030411537+618598847*1927816111+1624084534*386386406+1511477847*944062124+1840812326*769004148+185546252*1412058633+2145463598*1248006034+82870699*889698311+1625323762*485251122+1843639311*1079076214+1777269271*306760266+1645120956*1714190792)%2147483647=991461882
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 2 3 4 0 26%2147483647=1719499417 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+1112406525*2028950481+1345999435*43186015+752376469*1475067077+634588140*1069475621+1419170319*1582524202+1702860885*1151681172+710076517*720010503+1256487405*756841977+1114745059*36180608+1137838899*1544291561+1254184109*1640081406+1038210451*316471324+274378589*1973681341+171986381*1030411537+1536678585*1927816111+1305878831*386386406+1335902916*944062124+1755193245*769004148+2023391453*1412058633+293456010*1248006034+1751078325*889698311+1423042536*485251122+1749638204*1079076214+1345811362*306760266+1284924881*1714190792)%2147483647=1719499417
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 2 3 5 0 26%2147483647=1199346912 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+1796814865*2028950481+1253123171*43186015+1317611639*1475067077+1559245386*1069475621+1866942376*1582524202+1973593402*1151681172+47019780*720010503+1353487525*756841977+1840161555*36180608+2003659556*1544291561+200559114*1640081406+334988447*316471324+2023650872*1973681341+1296497964*1030411537+34285357*1927816111+1685894190*386386406+995962325*944062124+1295624230*769004148+1199631211*1412058633+1948677857*1248006034+1425322328*889698311+1466877680*485251122+702011012*1079076214+937706871*306760266+455802666*1714190792)%2147483647=1199346912
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 2 3 6 0 26%2147483647=1525617945 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+1838939499*2028950481+1353876630*43186015+1258713036*1475067077+1947503436*1069475621+1271796599*1582524202+1660157177*1151681172+564707688*720010503+1858113864*756841977+1015817431*36180608+1264608004*1544291561+735383960*1640081406+221696734*316471324+1297524163*1973681341+109088572*1030411537+792206628*1927816111+1921581249*386386406+94118806*944062124+476103426*769004148+239612482*1412058633+177052717*1248006034+826458039*889698311+1923715623*485251122+1014161165*1079076214+1341609618*306760266+786325583*1714190792)%2147483647=1525617945
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 2 3 7 0 26%2147483647=822708021 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*566056390+418714188*2028950481+1675147475*43186015+1674326661*1475067077+547797802*1069475621+2073962627*1582524202+897270857*1151681172+1582958967*720010503+49892701*756841977+1256824732*36180608+1435903714*1544291561+742583315*1640081406+1789294768*316471324+13407412*1973681341+518661610*1030411537+1259751297*1927816111+1695663205*386386406+2068940067*944062124+940478841*769004148+1982757556*1412058633+1956713516*1248006034+863066484*889698311+522298462*485251122+1343575777*1079076214+771712139*306760266+157728743*1714190792)%2147483647=822708021
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 2 3
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
end AspisR1.JFz_TX2_Q2_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2842525377#u64 2523923142#u64 6660615222#u64 2956302343#u64⟩,⟨pack 3819861949#u64 691995691#u64 5213098949#u64 1756661452#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4585014240014434928#u64 988471381467365327#u64 11141695764923836846#u64 4070004847196141655#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 206688657#u32 321894574#u32 1395506404#u32 787472842#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 206688657#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 321894574#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1395506404#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 787472842#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4303547321770831044#u64 401161029114697858#u64 8620214784798180460#u64 3180782782463587487#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 206688657#u32 321894574#u32 1395506404#u32 787472842#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 206688657#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 321894574#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1395506404#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 206688657#u32) (JFs_TX2_RawMath.extend 321894574#u32) (JFs_TX2_RawMath.extend 1395506404#u32) (JFs_TX2_RawMath.extend 787472842#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 787472842#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails12.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value0_3=
      ok (.Ok (pack 206688657#u32 321894574#u32 1395506404#u32 787472842#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (206688657<2147483647 ∧ 321894574<2147483647) ∧ (1395506404<2147483647 ∧ 787472842<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 206688657#u32 321894574#u32 1395506404#u32 787472842#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 206688657#u32 321894574#u32 1395506404#u32 787472842#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q2_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2842525377#u64 2523923142#u64 6660615222#u64 2956302343#u64⟩,⟨pack 3819861949#u64 691995691#u64 5213098949#u64 1756661452#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8335178522#u64 4690880637#u64 11845927618#u64 8171266874#u64⟩,⟨pack 7927363976#u64 2404050592#u64 10559328792#u64 4826133983#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7253912869833348533#u64 3879279417045628304#u64 10904218687379240013#u64 8882339527118371257#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1713902229#u32 1705879187#u32 1074238567#u32 1931651439#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1713902229#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1705879187#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1074238567#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1931651439#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5307854215350120249#u64 1510747624173297802#u64 9267533664717059275#u64 3265583444810338661#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1713902229#u32 1705879187#u32 1074238567#u32 1931651439#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1713902229#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1705879187#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1074238567#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1713902229#u32) (JFs_TX2_RawMath.extend 1705879187#u32) (JFs_TX2_RawMath.extend 1074238567#u32) (JFs_TX2_RawMath.extend 1931651439#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1931651439#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails12.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value1_3=
      ok (.Ok (pack 1713902229#u32 1705879187#u32 1074238567#u32 1931651439#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1713902229<2147483647 ∧ 1705879187<2147483647) ∧ (1074238567<2147483647 ∧ 1931651439<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1713902229#u32 1705879187#u32 1074238567#u32 1931651439#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2842525377#u64 2523923142#u64 6660615222#u64 2956302343#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1713902229#u32 1705879187#u32 1074238567#u32 1931651439#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3819861949#u64 691995691#u64 5213098949#u64 1756661452#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8335178522#u64 4690880637#u64 11845927618#u64 8171266874#u64⟩,⟨pack 7927363976#u64 2404050592#u64 10559328792#u64 4826133983#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10861434415#u64 5277540129#u64 18062939392#u64 11262824096#u64⟩,⟨pack 10813746495#u64 4432041085#u64 15658939340#u64 11853724847#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4413365158828884640#u64 1073194048252950026#u64 8922556938288987577#u64 3516701502383702178#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 872580461#u32 1143353706#u32 1719493458#u32 1855567867#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 872580461#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1143353706#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1719493458#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1855567867#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4047645655415550761#u64 3641959865205325686#u64 8610801556406039787#u64 10499333737323841025#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 872580461#u32 1143353706#u32 1719493458#u32 1855567867#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 872580461#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1143353706#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1719493458#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872580461#u32) (JFs_TX2_RawMath.extend 1143353706#u32) (JFs_TX2_RawMath.extend 1719493458#u32) (JFs_TX2_RawMath.extend 1855567867#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1855567867#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails12.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value2_3=
      ok (.Ok (pack 872580461#u32 1143353706#u32 1719493458#u32 1855567867#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (872580461<2147483647 ∧ 1143353706<2147483647) ∧ (1719493458<2147483647 ∧ 1855567867<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 872580461#u32 1143353706#u32 1719493458#u32 1855567867#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8335178522#u64 4690880637#u64 11845927618#u64 8171266874#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 872580461#u32 1143353706#u32 1719493458#u32 1855567867#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7927363976#u64 2404050592#u64 10559328792#u64 4826133983#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨124016180#u32,982572835#u32⟩,⟨883070216#u32,525405861#u32⟩⟩,⟨⟨76328260#u32,137073791#u32⟩,⟨626553811#u32,1116306612#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q2_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q2_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10861434415%2147483647 at h0
  norm_num at h0
  have e0 : a0=124016180#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5277540129%2147483647 at h1
  norm_num at h1
  have e1 : a1=982572835#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18062939392%2147483647 at h2
  norm_num at h2
  have e2 : a2=883070216#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11262824096%2147483647 at h3
  norm_num at h3
  have e3 : a3=525405861#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10813746495%2147483647 at h4
  norm_num at h4
  have e4 : a4=76328260#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=4432041085%2147483647 at h5
  norm_num at h5
  have e5 : a5=137073791#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15658939340%2147483647 at h6
  norm_num at h6
  have e6 : a6=626553811#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11853724847%2147483647 at h7
  norm_num at h7
  have e7 : a7=1116306612#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q2_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails12.value0_3
      from JFr_TX2_Tails12.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails12.value1_3
      from JFr_TX2_Tails12.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails12.value2_3
      from JFr_TX2_Tails12.source2_3,
    JFz_TX2_Q2_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q2_Raw30.after=JFz_TX2_Q2_Raw31.before := rfl
  have same2 : JFz_TX2_Q2_Raw31.after=JFz_TX2_Q2_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q2_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q2_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q2_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨312536918#u32,1609601714#u32⟩,⟨408026157#u32,1516867743#u32⟩⟩,⟨⟨1795827677#u32,1336420703#u32⟩,⟨4688109#u32,1939014633#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((312536918<2147483647 ∧ 1609601714<2147483647) ∧ (408026157<2147483647 ∧ 1516867743<2147483647)) ∧
    ((1795827677<2147483647 ∧ 1336420703<2147483647) ∧ (4688109<2147483647 ∧ 1939014633<2147483647))
  omega
theorem addition : decode JFz_TX2_Q2_Head3.value+decode JFz_TX2_Q2_Tail3.value=decode value := by
  change (⟨⟨⟨188520738,627028879⟩,⟨1672439588,991461882⟩⟩,⟨⟨1719499417,1199346912⟩,⟨1525617945,822708021⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨124016180,982572835⟩,⟨883070216,525405861⟩⟩,⟨⟨76328260,137073791⟩,⟨626553811,1116306612⟩⟩⟩=⟨⟨⟨312536918,1609601714⟩,⟨408026157,1516867743⟩⟩,⟨⟨1795827677,1336420703⟩,⟨4688109,1939014633⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 2 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q2_Head3.value JFz_TX2_Q2_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q2_Head3.source,
      JFz_TX2_Q2_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q2_Head3.value := by
    change ((188520738<2147483647 ∧ 627028879<2147483647) ∧ (1672439588<2147483647 ∧ 991461882<2147483647)) ∧
      ((1719499417<2147483647 ∧ 1199346912<2147483647) ∧ (1525617945<2147483647 ∧ 822708021<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q2_Tail3.value := by
    change ((124016180<2147483647 ∧ 982572835<2147483647) ∧ (883070216<2147483647 ∧ 525405861<2147483647)) ∧
      ((76328260<2147483647 ∧ 137073791<2147483647) ∧ (626553811<2147483647 ∧ 1116306612<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q2_Dot3
end
