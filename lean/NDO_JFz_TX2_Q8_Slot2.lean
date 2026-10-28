import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails18
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨913767031#u32,381963660#u32⟩,⟨1987327499#u32,1315284855#u32⟩⟩,⟨⟨95371028#u32,1813578436#u32⟩,⟨2058469312#u32,1690311527#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 8 2 0 0 26%2147483647=913767031 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1488207183+855639275*1675437278+867568255*439327401+352063*980025703+1106523000*1268499868+1554033304*960251116+1430280692*793347594+1491718280*1828889723+118514350*419671137+1675652887*442711851+1364884909*354247810+1135303194*1478433623+304762092*673692649+1465393816*790469611+824208172*1911109539+1752653420*1285088335+1385409049*1003467564+1003904973*277007323+1298953245*2117913769+2005758375*1449315559+497936241*1117396385+235809508*1506433842+1478307182*1600196305+1858903615*165438812+628035096*526155249+1244951250*1671917662)%2147483647=913767031
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 8 2 1 0 26%2147483647=381963660 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+1483149559*1675437278+655227887*439327401+39062738*980025703+729079828*1268499868+67370206*960251116+1685049618*793347594+385547620*1828889723+1786803209*419671137+779721715*442711851+594709522*354247810+338788461*1478433623+526756808*673692649+184076238*790469611+1852498770*1911109539+2102463508*1285088335+1086671526*1003467564+1147694576*277007323+1504805752*2117913769+2005073905*1449315559+185008025*1117396385+1485990146*1506433842+1255280192*1600196305+1018329259*165438812+570157693*526155249+1511904630*1671917662)%2147483647=381963660
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 8 2 2 0 26%2147483647=1987327499 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+1898717401*1675437278+1032732628*439327401+1313565596*980025703+1074182998*1268499868+1410213748*960251116+1182702806*793347594+321711020*1828889723+2062791928*419671137+1188803754*442711851+2038502201*354247810+735931834*1478433623+1330533011*673692649+1052874750*790469611+950153811*1911109539+1225424092*1285088335+1659116453*1003467564+1474177753*277007323+2073609211*2117913769+1602919019*1449315559+1865917845*1117396385+1085624123*1506433842+1837870964*1600196305+1550509101*165438812+1661725734*526155249+2066655336*1671917662)%2147483647=1987327499
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 8 2 3 0 26%2147483647=1315284855 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+1849775942*1675437278+656039795*439327401+1840648083*980025703+246996287*1268499868+1369248953*960251116+1132591724*793347594+92744917*1828889723+1719480363*419671137+1266677922*442711851+377386917*354247810+735227219*1478433623+465096431*673692649+451889791*790469611+1379836302*1911109539+618598847*1285088335+1624084534*1003467564+1511477847*277007323+1840812326*2117913769+185546252*1449315559+2145463598*1117396385+82870699*1506433842+1625323762*1600196305+1843639311*165438812+1777269271*526155249+1645120956*1671917662)%2147483647=1315284855
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 8 2 4 0 26%2147483647=95371028 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+1112406525*1675437278+1345999435*439327401+752376469*980025703+634588140*1268499868+1419170319*960251116+1702860885*793347594+710076517*1828889723+1256487405*419671137+1114745059*442711851+1137838899*354247810+1254184109*1478433623+1038210451*673692649+274378589*790469611+171986381*1911109539+1536678585*1285088335+1305878831*1003467564+1335902916*277007323+1755193245*2117913769+2023391453*1449315559+293456010*1117396385+1751078325*1506433842+1423042536*1600196305+1749638204*165438812+1345811362*526155249+1284924881*1671917662)%2147483647=95371028
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 8 2 5 0 26%2147483647=1813578436 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+1796814865*1675437278+1253123171*439327401+1317611639*980025703+1559245386*1268499868+1866942376*960251116+1973593402*793347594+47019780*1828889723+1353487525*419671137+1840161555*442711851+2003659556*354247810+200559114*1478433623+334988447*673692649+2023650872*790469611+1296497964*1911109539+34285357*1285088335+1685894190*1003467564+995962325*277007323+1295624230*2117913769+1199631211*1449315559+1948677857*1117396385+1425322328*1506433842+1466877680*1600196305+702011012*165438812+937706871*526155249+455802666*1671917662)%2147483647=1813578436
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 8 2 6 0 26%2147483647=2058469312 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+1838939499*1675437278+1353876630*439327401+1258713036*980025703+1947503436*1268499868+1271796599*960251116+1660157177*793347594+564707688*1828889723+1858113864*419671137+1015817431*442711851+1264608004*354247810+735383960*1478433623+221696734*673692649+1297524163*790469611+109088572*1911109539+792206628*1285088335+1921581249*1003467564+94118806*277007323+476103426*2117913769+239612482*1449315559+177052717*1117396385+826458039*1506433842+1923715623*1600196305+1014161165*165438812+1341609618*526155249+786325583*1671917662)%2147483647=2058469312
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 8 2 7 0 26%2147483647=1690311527 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1488207183+418714188*1675437278+1675147475*439327401+1674326661*980025703+547797802*1268499868+2073962627*960251116+897270857*793347594+1582958967*1828889723+49892701*419671137+1256824732*442711851+1435903714*354247810+742583315*1478433623+1789294768*673692649+13407412*790469611+518661610*1911109539+1259751297*1285088335+1695663205*1003467564+2068940067*277007323+940478841*2117913769+1982757556*1449315559+1956713516*1117396385+863066484*1506433842+522298462*1600196305+1343575777*165438812+771712139*526155249+157728743*1671917662)%2147483647=1690311527
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 8 2
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
end AspisR1.JFz_TX2_Q8_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4699390680#u64 1634689116#u64 6092391688#u64 2877024302#u64⟩,⟨pack 2226781792#u64 2458983849#u64 6707161857#u64 3218779361#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 7088534923603865839#u64 2979869845177901232#u64 11711939246289858470#u64 5718257741576093169#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1440831944#u32 413606107#u32 1485262239#u32 1272079585#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1440831944#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 413606107#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1485262239#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1272079585#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4741338621412426154#u64 1977965797932978902#u64 10399447621824587259#u64 6272342770913050584#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1440831944#u32 413606107#u32 1485262239#u32 1272079585#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1440831944#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 413606107#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1485262239#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1440831944#u32) (JFs_TX2_RawMath.extend 413606107#u32) (JFs_TX2_RawMath.extend 1485262239#u32) (JFs_TX2_RawMath.extend 1272079585#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1272079585#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails18.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value0_2=
      ok (.Ok (pack 1440831944#u32 413606107#u32 1485262239#u32 1272079585#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1440831944<2147483647 ∧ 413606107<2147483647) ∧ (1485262239<2147483647 ∧ 1272079585<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1440831944#u32 413606107#u32 1485262239#u32 1272079585#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1440831944#u32 413606107#u32 1485262239#u32 1272079585#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q8_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4699390680#u64 1634689116#u64 6092391688#u64 2877024302#u64⟩,⟨pack 2226781792#u64 2458983849#u64 6707161857#u64 3218779361#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8253960570#u64 4215566339#u64 10535511690#u64 5948819267#u64⟩,⟨pack 6527570048#u64 3361812091#u64 12316007894#u64 4275553889#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5998401117910809232#u64 2601263930787624993#u64 8968136067889377544#u64 5038766887630882690#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 954453558#u32 1181309782#u32 123969400#u32 1032949620#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 954453558#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1181309782#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 123969400#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1032949620#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4943924044536750254#u64 990471213255120942#u64 8820402605176879094#u64 1783681784903059260#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 954453558#u32 1181309782#u32 123969400#u32 1032949620#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 954453558#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1181309782#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 123969400#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 954453558#u32) (JFs_TX2_RawMath.extend 1181309782#u32) (JFs_TX2_RawMath.extend 123969400#u32) (JFs_TX2_RawMath.extend 1032949620#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1032949620#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails18.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value1_2=
      ok (.Ok (pack 954453558#u32 1181309782#u32 123969400#u32 1032949620#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (954453558<2147483647 ∧ 1181309782<2147483647) ∧ (123969400<2147483647 ∧ 1032949620<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 954453558#u32 1181309782#u32 123969400#u32 1032949620#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4699390680#u64 1634689116#u64 6092391688#u64 2877024302#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 954453558#u32 1181309782#u32 123969400#u32 1032949620#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2226781792#u64 2458983849#u64 6707161857#u64 3218779361#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8253960570#u64 4215566339#u64 10535511690#u64 5948819267#u64⟩,⟨pack 6527570048#u64 3361812091#u64 12316007894#u64 4275553889#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11835237210#u64 5961579718#u64 15453666640#u64 8966539577#u64⟩,⟨pack 8728419811#u64 6654815955#u64 17241130558#u64 7917267108#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 3695786271640243664#u64 926403348034981604#u64 8235436105664613316#u64 2076758064957653261#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 94236407#u32 1714241612#u32 763886170#u32 300124826#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 94236407#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1714241612#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 763886170#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 300124826#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 1611098051575202587#u64 3216937870220429427#u64 7089134947940438799#u64 5762866644898316519#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 94236407#u32 1714241612#u32 763886170#u32 300124826#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 94236407#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1714241612#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 763886170#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94236407#u32) (JFs_TX2_RawMath.extend 1714241612#u32) (JFs_TX2_RawMath.extend 763886170#u32) (JFs_TX2_RawMath.extend 300124826#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 300124826#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails18.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value2_2=
      ok (.Ok (pack 94236407#u32 1714241612#u32 763886170#u32 300124826#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (94236407<2147483647 ∧ 1714241612<2147483647) ∧ (763886170<2147483647 ∧ 300124826<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 94236407#u32 1714241612#u32 763886170#u32 300124826#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8253960570#u64 4215566339#u64 10535511690#u64 5948819267#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 94236407#u32 1714241612#u32 763886170#u32 300124826#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6527570048#u64 3361812091#u64 12316007894#u64 4275553889#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1097818975#u32,1666612424#u32⟩,⟨421281111#u32,376604989#u32⟩⟩,⟨⟨138485223#u32,212365014#u32⟩,⟨61261382#u32,1474816167#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q8_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q8_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11835237210%2147483647 at h0
  norm_num at h0
  have e0 : a0=1097818975#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5961579718%2147483647 at h1
  norm_num at h1
  have e1 : a1=1666612424#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15453666640%2147483647 at h2
  norm_num at h2
  have e2 : a2=421281111#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8966539577%2147483647 at h3
  norm_num at h3
  have e3 : a3=376604989#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8728419811%2147483647 at h4
  norm_num at h4
  have e4 : a4=138485223#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6654815955%2147483647 at h5
  norm_num at h5
  have e5 : a5=212365014#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17241130558%2147483647 at h6
  norm_num at h6
  have e6 : a6=61261382#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=7917267108%2147483647 at h7
  norm_num at h7
  have e7 : a7=1474816167#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q8_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails18.value0_2
      from JFr_TX2_Tails18.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails18.value1_2
      from JFr_TX2_Tails18.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails18.value2_2
      from JFr_TX2_Tails18.source2_2,
    JFz_TX2_Q8_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q8_Raw20.after=JFz_TX2_Q8_Raw21.before := rfl
  have same2 : JFz_TX2_Q8_Raw21.after=JFz_TX2_Q8_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q8_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q8_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q8_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨2011586006#u32,2048576084#u32⟩,⟨261124963#u32,1691889844#u32⟩⟩,⟨⟨233856251#u32,2025943450#u32⟩,⟨2119730694#u32,1017644047#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2011586006<2147483647 ∧ 2048576084<2147483647) ∧ (261124963<2147483647 ∧ 1691889844<2147483647)) ∧
    ((233856251<2147483647 ∧ 2025943450<2147483647) ∧ (2119730694<2147483647 ∧ 1017644047<2147483647))
  omega
theorem addition : decode JFz_TX2_Q8_Head2.value+decode JFz_TX2_Q8_Tail2.value=decode value := by
  change (⟨⟨⟨913767031,381963660⟩,⟨1987327499,1315284855⟩⟩,⟨⟨95371028,1813578436⟩,⟨2058469312,1690311527⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1097818975,1666612424⟩,⟨421281111,376604989⟩⟩,⟨⟨138485223,212365014⟩,⟨61261382,1474816167⟩⟩⟩=⟨⟨⟨2011586006,2048576084⟩,⟨261124963,1691889844⟩⟩,⟨⟨233856251,2025943450⟩,⟨2119730694,1017644047⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 8 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q8_Head2.value JFz_TX2_Q8_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q8_Head2.source,
      JFz_TX2_Q8_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q8_Head2.value := by
    change ((913767031<2147483647 ∧ 381963660<2147483647) ∧ (1987327499<2147483647 ∧ 1315284855<2147483647)) ∧
      ((95371028<2147483647 ∧ 1813578436<2147483647) ∧ (2058469312<2147483647 ∧ 1690311527<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q8_Tail2.value := by
    change ((1097818975<2147483647 ∧ 1666612424<2147483647) ∧ (421281111<2147483647 ∧ 376604989<2147483647)) ∧
      ((138485223<2147483647 ∧ 212365014<2147483647) ∧ (61261382<2147483647 ∧ 1474816167<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q8_Dot2
end
