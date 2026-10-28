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
namespace AspisR1.JFz_TX2_Q10_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨773868638#u32,690047232#u32⟩,⟨1079743855#u32,1919589280#u32⟩⟩,⟨⟨852303943#u32,1948539469#u32⟩,⟨1614716542#u32,2099690874#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 10 3 0 0 26%2147483647=773868638 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1949166271+855639275*1148392626+867568255*1294047668+352063*396514373+1106523000*2091666522+1554033304*229994+1430280692*2026088164+1491718280*1709280386+118514350*1547147622+1675652887*108363953+1364884909*1778793238+1135303194*1743649878+304762092*1636516714+1465393816*330673714+824208172*808091691+1752653420*1595216755+1385409049*103367617+1003904973*1671487815+1298953245*238348162+2005758375*446208195+497936241*1180956870+235809508*268867557+1478307182*1666604641+1858903615*1814761522+628035096*1007454433+1244951250*1712224225)%2147483647=773868638
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 10 3 1 0 26%2147483647=690047232 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+1483149559*1148392626+655227887*1294047668+39062738*396514373+729079828*2091666522+67370206*229994+1685049618*2026088164+385547620*1709280386+1786803209*1547147622+779721715*108363953+594709522*1778793238+338788461*1743649878+526756808*1636516714+184076238*330673714+1852498770*808091691+2102463508*1595216755+1086671526*103367617+1147694576*1671487815+1504805752*238348162+2005073905*446208195+185008025*1180956870+1485990146*268867557+1255280192*1666604641+1018329259*1814761522+570157693*1007454433+1511904630*1712224225)%2147483647=690047232
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 10 3 2 0 26%2147483647=1079743855 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+1898717401*1148392626+1032732628*1294047668+1313565596*396514373+1074182998*2091666522+1410213748*229994+1182702806*2026088164+321711020*1709280386+2062791928*1547147622+1188803754*108363953+2038502201*1778793238+735931834*1743649878+1330533011*1636516714+1052874750*330673714+950153811*808091691+1225424092*1595216755+1659116453*103367617+1474177753*1671487815+2073609211*238348162+1602919019*446208195+1865917845*1180956870+1085624123*268867557+1837870964*1666604641+1550509101*1814761522+1661725734*1007454433+2066655336*1712224225)%2147483647=1079743855
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 10 3 3 0 26%2147483647=1919589280 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+1849775942*1148392626+656039795*1294047668+1840648083*396514373+246996287*2091666522+1369248953*229994+1132591724*2026088164+92744917*1709280386+1719480363*1547147622+1266677922*108363953+377386917*1778793238+735227219*1743649878+465096431*1636516714+451889791*330673714+1379836302*808091691+618598847*1595216755+1624084534*103367617+1511477847*1671487815+1840812326*238348162+185546252*446208195+2145463598*1180956870+82870699*268867557+1625323762*1666604641+1843639311*1814761522+1777269271*1007454433+1645120956*1712224225)%2147483647=1919589280
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 10 3 4 0 26%2147483647=852303943 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+1112406525*1148392626+1345999435*1294047668+752376469*396514373+634588140*2091666522+1419170319*229994+1702860885*2026088164+710076517*1709280386+1256487405*1547147622+1114745059*108363953+1137838899*1778793238+1254184109*1743649878+1038210451*1636516714+274378589*330673714+171986381*808091691+1536678585*1595216755+1305878831*103367617+1335902916*1671487815+1755193245*238348162+2023391453*446208195+293456010*1180956870+1751078325*268867557+1423042536*1666604641+1749638204*1814761522+1345811362*1007454433+1284924881*1712224225)%2147483647=852303943
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 10 3 5 0 26%2147483647=1948539469 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+1796814865*1148392626+1253123171*1294047668+1317611639*396514373+1559245386*2091666522+1866942376*229994+1973593402*2026088164+47019780*1709280386+1353487525*1547147622+1840161555*108363953+2003659556*1778793238+200559114*1743649878+334988447*1636516714+2023650872*330673714+1296497964*808091691+34285357*1595216755+1685894190*103367617+995962325*1671487815+1295624230*238348162+1199631211*446208195+1948677857*1180956870+1425322328*268867557+1466877680*1666604641+702011012*1814761522+937706871*1007454433+455802666*1712224225)%2147483647=1948539469
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 10 3 6 0 26%2147483647=1614716542 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+1838939499*1148392626+1353876630*1294047668+1258713036*396514373+1947503436*2091666522+1271796599*229994+1660157177*2026088164+564707688*1709280386+1858113864*1547147622+1015817431*108363953+1264608004*1778793238+735383960*1743649878+221696734*1636516714+1297524163*330673714+109088572*808091691+792206628*1595216755+1921581249*103367617+94118806*1671487815+476103426*238348162+239612482*446208195+177052717*1180956870+826458039*268867557+1923715623*1666604641+1014161165*1814761522+1341609618*1007454433+786325583*1712224225)%2147483647=1614716542
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 10 3 7 0 26%2147483647=2099690874 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1949166271+418714188*1148392626+1675147475*1294047668+1674326661*396514373+547797802*2091666522+2073962627*229994+897270857*2026088164+1582958967*1709280386+49892701*1547147622+1256824732*108363953+1435903714*1778793238+742583315*1743649878+1789294768*1636516714+13407412*330673714+518661610*808091691+1259751297*1595216755+1695663205*103367617+2068940067*1671487815+940478841*238348162+1982757556*446208195+1956713516*1180956870+863066484*268867557+522298462*1666604641+1343575777*1814761522+771712139*1007454433+157728743*1712224225)%2147483647=2099690874
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 10 3
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
end AspisR1.JFz_TX2_Q10_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2749898053#u64 4258683738#u64 7555970724#u64 4254821182#u64⟩,⟨pack 3246597337#u64 1753170611#u64 5217997395#u64 6419513185#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5380098091465848794#u64 6196979560665721651#u64 13221976547048762217#u64 5367699441515994839#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1594972266#u32 1814327987#u32 1706401827#u32 342784780#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1594972266#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1814327987#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1706401827#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 342784780#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3067187317855844255#u64 2796194963378084273#u64 9048777109708530854#u64 9328987380682821169#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1594972266#u32 1814327987#u32 1706401827#u32 342784780#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1594972266#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1814327987#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1706401827#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1594972266#u32) (JFs_TX2_RawMath.extend 1814327987#u32) (JFs_TX2_RawMath.extend 1706401827#u32) (JFs_TX2_RawMath.extend 342784780#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 342784780#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails20.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value0_3=
      ok (.Ok (pack 1594972266#u32 1814327987#u32 1706401827#u32 342784780#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1594972266<2147483647 ∧ 1814327987<2147483647) ∧ (1706401827<2147483647 ∧ 342784780<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1594972266#u32 1814327987#u32 1706401827#u32 342784780#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1594972266#u32 1814327987#u32 1706401827#u32 342784780#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q10_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2749898053#u64 4258683738#u64 7555970724#u64 4254821182#u64⟩,⟨pack 3246597337#u64 1753170611#u64 5217997395#u64 6419513185#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6980901646#u64 5779354823#u64 13332702699#u64 8586798094#u64⟩,⟨pack 6634739125#u64 3708057055#u64 10067268693#u64 8117501841#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4605647764646978895#u64 1581473417347894794#u64 11308399666811563037#u64 5255512825699634861#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 150667993#u32 800728755#u32 1845696287#u32 1668024151#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 150667993#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 800728755#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1845696287#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1668024151#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4516891201669201825#u64 552407083865087115#u64 9625885177370507999#u64 1972132209384515737#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 150667993#u32 800728755#u32 1845696287#u32 1668024151#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 150667993#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 800728755#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1845696287#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 150667993#u32) (JFs_TX2_RawMath.extend 800728755#u32) (JFs_TX2_RawMath.extend 1845696287#u32) (JFs_TX2_RawMath.extend 1668024151#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1668024151#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails20.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value1_3=
      ok (.Ok (pack 150667993#u32 800728755#u32 1845696287#u32 1668024151#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (150667993<2147483647 ∧ 800728755<2147483647) ∧ (1845696287<2147483647 ∧ 1668024151<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 150667993#u32 800728755#u32 1845696287#u32 1668024151#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2749898053#u64 4258683738#u64 7555970724#u64 4254821182#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 150667993#u32 800728755#u32 1845696287#u32 1668024151#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3246597337#u64 1753170611#u64 5217997395#u64 6419513185#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6980901646#u64 5779354823#u64 13332702699#u64 8586798094#u64⟩,⟨pack 6634739125#u64 3708057055#u64 10067268693#u64 8117501841#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10097832077#u64 6452269359#u64 18213149500#u64 10372932476#u64⟩,⟨pack 10800732783#u64 5407189749#u64 15149946845#u64 10739006849#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4682793869430969618#u64 715617748868077390#u64 8839427965236136836#u64 1919279778619257306#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 761792134#u32 563810070#u32 333616994#u32 1357603558#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 761792134#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 563810070#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 333616994#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1357603558#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4921971807284842027#u64 2408532426548383264#u64 7895630087508045842#u64 5619057223180955748#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 761792134#u32 563810070#u32 333616994#u32 1357603558#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 761792134#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 563810070#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 333616994#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 761792134#u32) (JFs_TX2_RawMath.extend 563810070#u32) (JFs_TX2_RawMath.extend 333616994#u32) (JFs_TX2_RawMath.extend 1357603558#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1357603558#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails20.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value2_3=
      ok (.Ok (pack 761792134#u32 563810070#u32 333616994#u32 1357603558#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (761792134<2147483647 ∧ 563810070<2147483647) ∧ (333616994<2147483647 ∧ 1357603558<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 761792134#u32 563810070#u32 333616994#u32 1357603558#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6980901646#u64 5779354823#u64 13332702699#u64 8586798094#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 761792134#u32 563810070#u32 333616994#u32 1357603558#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6634739125#u64 3708057055#u64 10067268693#u64 8117501841#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1507897489#u32,9818418#u32⟩,⟨1033280324#u32,1782997888#u32⟩⟩,⟨⟨63314548#u32,1112222455#u32⟩,⟨117561316#u32,1588614#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q10_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q10_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10097832077%2147483647 at h0
  norm_num at h0
  have e0 : a0=1507897489#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6452269359%2147483647 at h1
  norm_num at h1
  have e1 : a1=9818418#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18213149500%2147483647 at h2
  norm_num at h2
  have e2 : a2=1033280324#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10372932476%2147483647 at h3
  norm_num at h3
  have e3 : a3=1782997888#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10800732783%2147483647 at h4
  norm_num at h4
  have e4 : a4=63314548#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5407189749%2147483647 at h5
  norm_num at h5
  have e5 : a5=1112222455#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15149946845%2147483647 at h6
  norm_num at h6
  have e6 : a6=117561316#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10739006849%2147483647 at h7
  norm_num at h7
  have e7 : a7=1588614#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q10_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails20.value0_3
      from JFr_TX2_Tails20.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails20.value1_3
      from JFr_TX2_Tails20.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails20.value2_3
      from JFr_TX2_Tails20.source2_3,
    JFz_TX2_Q10_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q10_Raw30.after=JFz_TX2_Q10_Raw31.before := rfl
  have same2 : JFz_TX2_Q10_Raw31.after=JFz_TX2_Q10_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q10_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q10_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q10_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨134282480#u32,699865650#u32⟩,⟨2113024179#u32,1555103521#u32⟩⟩,⟨⟨915618491#u32,913278277#u32⟩,⟨1732277858#u32,2101279488#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((134282480<2147483647 ∧ 699865650<2147483647) ∧ (2113024179<2147483647 ∧ 1555103521<2147483647)) ∧
    ((915618491<2147483647 ∧ 913278277<2147483647) ∧ (1732277858<2147483647 ∧ 2101279488<2147483647))
  omega
theorem addition : decode JFz_TX2_Q10_Head3.value+decode JFz_TX2_Q10_Tail3.value=decode value := by
  change (⟨⟨⟨773868638,690047232⟩,⟨1079743855,1919589280⟩⟩,⟨⟨852303943,1948539469⟩,⟨1614716542,2099690874⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1507897489,9818418⟩,⟨1033280324,1782997888⟩⟩,⟨⟨63314548,1112222455⟩,⟨117561316,1588614⟩⟩⟩=⟨⟨⟨134282480,699865650⟩,⟨2113024179,1555103521⟩⟩,⟨⟨915618491,913278277⟩,⟨1732277858,2101279488⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 10 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q10_Head3.value JFz_TX2_Q10_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q10_Head3.source,
      JFz_TX2_Q10_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q10_Head3.value := by
    change ((773868638<2147483647 ∧ 690047232<2147483647) ∧ (1079743855<2147483647 ∧ 1919589280<2147483647)) ∧
      ((852303943<2147483647 ∧ 1948539469<2147483647) ∧ (1614716542<2147483647 ∧ 2099690874<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q10_Tail3.value := by
    change ((1507897489<2147483647 ∧ 9818418<2147483647) ∧ (1033280324<2147483647 ∧ 1782997888<2147483647)) ∧
      ((63314548<2147483647 ∧ 1112222455<2147483647) ∧ (117561316<2147483647 ∧ 1588614<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q10_Dot3
end
