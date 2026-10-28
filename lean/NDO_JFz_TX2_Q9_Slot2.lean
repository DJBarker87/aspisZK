import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails19
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1209992379#u32,1600988911#u32⟩,⟨1553883385#u32,834820198#u32⟩⟩,⟨⟨613144168#u32,1532944048#u32⟩,⟨147821819#u32,1591066896#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 9 2 0 0 26%2147483647=1209992379 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1783045312+855639275*894191220+867568255*2079401594+352063*1432816893+1106523000*1424527041+1554033304*771669691+1430280692*613337743+1491718280*678551281+118514350*1152308811+1675652887*1437200783+1364884909*1730530982+1135303194*56828082+304762092*1935150966+1465393816*1922467946+824208172*97642027+1752653420*1845010961+1385409049*1214348379+1003904973*727038455+1298953245*828402176+2005758375*1317566038+497936241*703254767+235809508*1417629745+1478307182*876638745+1858903615*1898981816+628035096*246978350+1244951250*816149766)%2147483647=1209992379
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 9 2 1 0 26%2147483647=1600988911 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+1483149559*894191220+655227887*2079401594+39062738*1432816893+729079828*1424527041+67370206*771669691+1685049618*613337743+385547620*678551281+1786803209*1152308811+779721715*1437200783+594709522*1730530982+338788461*56828082+526756808*1935150966+184076238*1922467946+1852498770*97642027+2102463508*1845010961+1086671526*1214348379+1147694576*727038455+1504805752*828402176+2005073905*1317566038+185008025*703254767+1485990146*1417629745+1255280192*876638745+1018329259*1898981816+570157693*246978350+1511904630*816149766)%2147483647=1600988911
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 9 2 2 0 26%2147483647=1553883385 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+1898717401*894191220+1032732628*2079401594+1313565596*1432816893+1074182998*1424527041+1410213748*771669691+1182702806*613337743+321711020*678551281+2062791928*1152308811+1188803754*1437200783+2038502201*1730530982+735931834*56828082+1330533011*1935150966+1052874750*1922467946+950153811*97642027+1225424092*1845010961+1659116453*1214348379+1474177753*727038455+2073609211*828402176+1602919019*1317566038+1865917845*703254767+1085624123*1417629745+1837870964*876638745+1550509101*1898981816+1661725734*246978350+2066655336*816149766)%2147483647=1553883385
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 9 2 3 0 26%2147483647=834820198 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+1849775942*894191220+656039795*2079401594+1840648083*1432816893+246996287*1424527041+1369248953*771669691+1132591724*613337743+92744917*678551281+1719480363*1152308811+1266677922*1437200783+377386917*1730530982+735227219*56828082+465096431*1935150966+451889791*1922467946+1379836302*97642027+618598847*1845010961+1624084534*1214348379+1511477847*727038455+1840812326*828402176+185546252*1317566038+2145463598*703254767+82870699*1417629745+1625323762*876638745+1843639311*1898981816+1777269271*246978350+1645120956*816149766)%2147483647=834820198
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 9 2 4 0 26%2147483647=613144168 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+1112406525*894191220+1345999435*2079401594+752376469*1432816893+634588140*1424527041+1419170319*771669691+1702860885*613337743+710076517*678551281+1256487405*1152308811+1114745059*1437200783+1137838899*1730530982+1254184109*56828082+1038210451*1935150966+274378589*1922467946+171986381*97642027+1536678585*1845010961+1305878831*1214348379+1335902916*727038455+1755193245*828402176+2023391453*1317566038+293456010*703254767+1751078325*1417629745+1423042536*876638745+1749638204*1898981816+1345811362*246978350+1284924881*816149766)%2147483647=613144168
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 9 2 5 0 26%2147483647=1532944048 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+1796814865*894191220+1253123171*2079401594+1317611639*1432816893+1559245386*1424527041+1866942376*771669691+1973593402*613337743+47019780*678551281+1353487525*1152308811+1840161555*1437200783+2003659556*1730530982+200559114*56828082+334988447*1935150966+2023650872*1922467946+1296497964*97642027+34285357*1845010961+1685894190*1214348379+995962325*727038455+1295624230*828402176+1199631211*1317566038+1948677857*703254767+1425322328*1417629745+1466877680*876638745+702011012*1898981816+937706871*246978350+455802666*816149766)%2147483647=1532944048
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 9 2 6 0 26%2147483647=147821819 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+1838939499*894191220+1353876630*2079401594+1258713036*1432816893+1947503436*1424527041+1271796599*771669691+1660157177*613337743+564707688*678551281+1858113864*1152308811+1015817431*1437200783+1264608004*1730530982+735383960*56828082+221696734*1935150966+1297524163*1922467946+109088572*97642027+792206628*1845010961+1921581249*1214348379+94118806*727038455+476103426*828402176+239612482*1317566038+177052717*703254767+826458039*1417629745+1923715623*876638745+1014161165*1898981816+1341609618*246978350+786325583*816149766)%2147483647=147821819
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 9 2 7 0 26%2147483647=1591066896 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1783045312+418714188*894191220+1675147475*2079401594+1674326661*1432816893+547797802*1424527041+2073962627*771669691+897270857*613337743+1582958967*678551281+49892701*1152308811+1256824732*1437200783+1435903714*1730530982+742583315*56828082+1789294768*1935150966+13407412*1922467946+518661610*97642027+1259751297*1845010961+1695663205*1214348379+2068940067*727038455+940478841*828402176+1982757556*1317566038+1956713516*703254767+863066484*1417629745+522298462*876638745+1343575777*1898981816+771712139*246978350+157728743*816149766)%2147483647=1591066896
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 9)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 9 2
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
end AspisR1.JFz_TX2_Q9_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4874036656#u64 2282039959#u64 5445187320#u64 5212714147#u64⟩,⟨pack 3790639931#u64 2915543448#u64 6209299912#u64 4835785165#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 6875377543813228235#u64 3447668380588573271#u64 10409411749263680845#u64 6778742863096043316#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1474522468#u32 609606155#u32 1269350876#u32 1827573796#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1474522468#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 609606155#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1269350876#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1827573796#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4512499226498914037#u64 2107543707519068653#u64 9271855822164584011#u64 6724726527941290882#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1474522468#u32 609606155#u32 1269350876#u32 1827573796#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1474522468#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 609606155#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1269350876#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1474522468#u32) (JFs_TX2_RawMath.extend 609606155#u32) (JFs_TX2_RawMath.extend 1269350876#u32) (JFs_TX2_RawMath.extend 1827573796#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1827573796#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails19.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails19.value0_2=
      ok (.Ok (pack 1474522468#u32 609606155#u32 1269350876#u32 1827573796#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1474522468<2147483647 ∧ 609606155<2147483647) ∧ (1269350876<2147483647 ∧ 1827573796<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1474522468#u32 609606155#u32 1269350876#u32 1827573796#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1474522468#u32 609606155#u32 1269350876#u32 1827573796#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q9_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4874036656#u64 2282039959#u64 5445187320#u64 5212714147#u64⟩,⟨pack 3790639931#u64 2915543448#u64 6209299912#u64 4835785165#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8343399815#u64 3946795456#u64 11364096009#u64 7869346316#u64⟩,⟨pack 7319057030#u64 4316779546#u64 11000611342#u64 5644212213#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4223730761625165400#u64 3514350837439606842#u64 10139573473792319581#u64 3993180206415461614#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 145318559#u32 1815785660#u32 1660711922#u32 245064003#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 145318559#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1815785660#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1660711922#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 245064003#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4270123709903819140#u64 1205608994548141190#u64 9265936297106025558#u64 1474015503898254227#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 145318559#u32 1815785660#u32 1660711922#u32 245064003#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 145318559#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1815785660#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1660711922#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 145318559#u32) (JFs_TX2_RawMath.extend 1815785660#u32) (JFs_TX2_RawMath.extend 1660711922#u32) (JFs_TX2_RawMath.extend 245064003#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 245064003#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails19.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails19.value1_2=
      ok (.Ok (pack 145318559#u32 1815785660#u32 1660711922#u32 245064003#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (145318559<2147483647 ∧ 1815785660<2147483647) ∧ (1660711922<2147483647 ∧ 245064003<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 145318559#u32 1815785660#u32 1660711922#u32 245064003#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4874036656#u64 2282039959#u64 5445187320#u64 5212714147#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 145318559#u32 1815785660#u32 1660711922#u32 245064003#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3790639931#u64 2915543448#u64 6209299912#u64 4835785165#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q9_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8343399815#u64 3946795456#u64 11364096009#u64 7869346316#u64⟩,⟨pack 7319057030#u64 4316779546#u64 11000611342#u64 5644212213#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10638320447#u64 4829934453#u64 17133086431#u64 10401244690#u64⟩,⟨pack 9694546017#u64 5218944757#u64 15083815401#u64 8954381128#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4691228804269770300#u64 322636393525225863#u64 8605072753605023407#u64 1513964714410137153#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 385472759#u32 207821451#u32 335060219#u32 1695091405#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 385472759#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 207821451#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 335060219#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1695091405#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4911856440257429258#u64 1081224840691802708#u64 7125341263688902554#u64 4775173831524582586#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 385472759#u32 207821451#u32 335060219#u32 1695091405#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 385472759#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 207821451#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 335060219#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 385472759#u32) (JFs_TX2_RawMath.extend 207821451#u32) (JFs_TX2_RawMath.extend 335060219#u32) (JFs_TX2_RawMath.extend 1695091405#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1695091405#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails19.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails19.value2_2=
      ok (.Ok (pack 385472759#u32 207821451#u32 335060219#u32 1695091405#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (385472759<2147483647 ∧ 207821451<2147483647) ∧ (335060219<2147483647 ∧ 1695091405<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 385472759#u32 207821451#u32 335060219#u32 1695091405#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8343399815#u64 3946795456#u64 11364096009#u64 7869346316#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 385472759#u32 207821451#u32 335060219#u32 1695091405#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7319057030#u64 4316779546#u64 11000611342#u64 5644212213#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q9_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨2048385859#u32,534967159#u32⟩,⟨2100700902#u32,1811310102#u32⟩⟩,⟨⟨1104611429#u32,923977463#u32⟩,⟨51429872#u32,364446540#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q9_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q9_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10638320447%2147483647 at h0
  norm_num at h0
  have e0 : a0=2048385859#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=4829934453%2147483647 at h1
  norm_num at h1
  have e1 : a1=534967159#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17133086431%2147483647 at h2
  norm_num at h2
  have e2 : a2=2100700902#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10401244690%2147483647 at h3
  norm_num at h3
  have e3 : a3=1811310102#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9694546017%2147483647 at h4
  norm_num at h4
  have e4 : a4=1104611429#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5218944757%2147483647 at h5
  norm_num at h5
  have e5 : a5=923977463#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15083815401%2147483647 at h6
  norm_num at h6
  have e6 : a6=51429872#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8954381128%2147483647 at h7
  norm_num at h7
  have e7 : a7=364446540#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 9)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q9_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 9))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails19.value0_2
      from JFr_TX2_Tails19.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 9))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails19.value1_2
      from JFr_TX2_Tails19.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 9))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails19.value2_2
      from JFr_TX2_Tails19.source2_2,
    JFz_TX2_Q9_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q9_Raw20.after=JFz_TX2_Q9_Raw21.before := rfl
  have same2 : JFz_TX2_Q9_Raw21.after=JFz_TX2_Q9_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q9_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q9_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q9_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1110894591#u32,2135956070#u32⟩,⟨1507100640#u32,498646653#u32⟩⟩,⟨⟨1717755597#u32,309437864#u32⟩,⟨199251691#u32,1955513436#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1110894591<2147483647 ∧ 2135956070<2147483647) ∧ (1507100640<2147483647 ∧ 498646653<2147483647)) ∧
    ((1717755597<2147483647 ∧ 309437864<2147483647) ∧ (199251691<2147483647 ∧ 1955513436<2147483647))
  omega
theorem addition : decode JFz_TX2_Q9_Head2.value+decode JFz_TX2_Q9_Tail2.value=decode value := by
  change (⟨⟨⟨1209992379,1600988911⟩,⟨1553883385,834820198⟩⟩,⟨⟨613144168,1532944048⟩,⟨147821819,1591066896⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨2048385859,534967159⟩,⟨2100700902,1811310102⟩⟩,⟨⟨1104611429,923977463⟩,⟨51429872,364446540⟩⟩⟩=⟨⟨⟨1110894591,2135956070⟩,⟨1507100640,498646653⟩⟩,⟨⟨1717755597,309437864⟩,⟨199251691,1955513436⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 9)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 9 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q9_Head2.value JFz_TX2_Q9_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q9_Head2.source,
      JFz_TX2_Q9_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q9_Head2.value := by
    change ((1209992379<2147483647 ∧ 1600988911<2147483647) ∧ (1553883385<2147483647 ∧ 834820198<2147483647)) ∧
      ((613144168<2147483647 ∧ 1532944048<2147483647) ∧ (147821819<2147483647 ∧ 1591066896<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q9_Tail2.value := by
    change ((2048385859<2147483647 ∧ 534967159<2147483647) ∧ (2100700902<2147483647 ∧ 1811310102<2147483647)) ∧
      ((1104611429<2147483647 ∧ 923977463<2147483647) ∧ (51429872<2147483647 ∧ 364446540<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q9_Dot2
end
