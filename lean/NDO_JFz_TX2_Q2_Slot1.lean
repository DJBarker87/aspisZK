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
namespace AspisR1.JFz_TX2_Q2_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨240096317#u32,1501185053#u32⟩,⟨139913307#u32,2037768087#u32⟩⟩,⟨⟨2089294135#u32,782467156#u32⟩,⟨483822967#u32,1194991360#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 2 1 0 0 26%2147483647=240096317 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1003235730+855639275*1841258068+867568255*1961934587+352063*91747854+1106523000*1097617578+1554033304*1668958178+1430280692*2083586784+1491718280*880283253+118514350*1393468378+1675652887*2127193348+1364884909*1301412370+1135303194*118902098+304762092*1677278404+1465393816*1255748993+824208172*462686357+1752653420*1701970755+1385409049*594418581+1003904973*624070534+1298953245*950043201+2005758375*1921501063+497936241*1281622294+235809508*456476710+1478307182*849502879+1858903615*862165687+628035096*344040777+1244951250*7311885)%2147483647=240096317
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 2 1 1 0 26%2147483647=1501185053 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+1483149559*1841258068+655227887*1961934587+39062738*91747854+729079828*1097617578+67370206*1668958178+1685049618*2083586784+385547620*880283253+1786803209*1393468378+779721715*2127193348+594709522*1301412370+338788461*118902098+526756808*1677278404+184076238*1255748993+1852498770*462686357+2102463508*1701970755+1086671526*594418581+1147694576*624070534+1504805752*950043201+2005073905*1921501063+185008025*1281622294+1485990146*456476710+1255280192*849502879+1018329259*862165687+570157693*344040777+1511904630*7311885)%2147483647=1501185053
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 2 1 2 0 26%2147483647=139913307 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+1898717401*1841258068+1032732628*1961934587+1313565596*91747854+1074182998*1097617578+1410213748*1668958178+1182702806*2083586784+321711020*880283253+2062791928*1393468378+1188803754*2127193348+2038502201*1301412370+735931834*118902098+1330533011*1677278404+1052874750*1255748993+950153811*462686357+1225424092*1701970755+1659116453*594418581+1474177753*624070534+2073609211*950043201+1602919019*1921501063+1865917845*1281622294+1085624123*456476710+1837870964*849502879+1550509101*862165687+1661725734*344040777+2066655336*7311885)%2147483647=139913307
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 2 1 3 0 26%2147483647=2037768087 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+1849775942*1841258068+656039795*1961934587+1840648083*91747854+246996287*1097617578+1369248953*1668958178+1132591724*2083586784+92744917*880283253+1719480363*1393468378+1266677922*2127193348+377386917*1301412370+735227219*118902098+465096431*1677278404+451889791*1255748993+1379836302*462686357+618598847*1701970755+1624084534*594418581+1511477847*624070534+1840812326*950043201+185546252*1921501063+2145463598*1281622294+82870699*456476710+1625323762*849502879+1843639311*862165687+1777269271*344040777+1645120956*7311885)%2147483647=2037768087
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 2 1 4 0 26%2147483647=2089294135 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+1112406525*1841258068+1345999435*1961934587+752376469*91747854+634588140*1097617578+1419170319*1668958178+1702860885*2083586784+710076517*880283253+1256487405*1393468378+1114745059*2127193348+1137838899*1301412370+1254184109*118902098+1038210451*1677278404+274378589*1255748993+171986381*462686357+1536678585*1701970755+1305878831*594418581+1335902916*624070534+1755193245*950043201+2023391453*1921501063+293456010*1281622294+1751078325*456476710+1423042536*849502879+1749638204*862165687+1345811362*344040777+1284924881*7311885)%2147483647=2089294135
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 2 1 5 0 26%2147483647=782467156 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+1796814865*1841258068+1253123171*1961934587+1317611639*91747854+1559245386*1097617578+1866942376*1668958178+1973593402*2083586784+47019780*880283253+1353487525*1393468378+1840161555*2127193348+2003659556*1301412370+200559114*118902098+334988447*1677278404+2023650872*1255748993+1296497964*462686357+34285357*1701970755+1685894190*594418581+995962325*624070534+1295624230*950043201+1199631211*1921501063+1948677857*1281622294+1425322328*456476710+1466877680*849502879+702011012*862165687+937706871*344040777+455802666*7311885)%2147483647=782467156
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 2 1 6 0 26%2147483647=483822967 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+1838939499*1841258068+1353876630*1961934587+1258713036*91747854+1947503436*1097617578+1271796599*1668958178+1660157177*2083586784+564707688*880283253+1858113864*1393468378+1015817431*2127193348+1264608004*1301412370+735383960*118902098+221696734*1677278404+1297524163*1255748993+109088572*462686357+792206628*1701970755+1921581249*594418581+94118806*624070534+476103426*950043201+239612482*1921501063+177052717*1281622294+826458039*456476710+1923715623*849502879+1014161165*862165687+1341609618*344040777+786325583*7311885)%2147483647=483822967
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 2 1 7 0 26%2147483647=1194991360 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1003235730+418714188*1841258068+1675147475*1961934587+1674326661*91747854+547797802*1097617578+2073962627*1668958178+897270857*2083586784+1582958967*880283253+49892701*1393468378+1256824732*2127193348+1435903714*1301412370+742583315*118902098+1789294768*1677278404+13407412*1255748993+518661610*462686357+1259751297*1701970755+1695663205*594418581+2068940067*624070534+940478841*950043201+1982757556*1921501063+1956713516*1281622294+863066484*456476710+522298462*849502879+1343575777*862165687+771712139*344040777+157728743*7311885)%2147483647=1194991360
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 2 1
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
end AspisR1.JFz_TX2_Q2_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3384472310#u64 3028433463#u64 7157945013#u64 3965799336#u64⟩,⟨pack 2265226802#u64 2913002714#u64 2939808489#u64 6170857875#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 3561427889769511775#u64 5185801884557042570#u64 11205217397544040192#u64 8411866680328151885#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 793247536#u32 1886954598#u32 2005296707#u32 1654813484#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 793247536#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1886954598#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2005296707#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1654813484#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2618271661653798346#u64 1830993151457683383#u64 5752399229080349099#u64 8764084655970271349#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 793247536#u32 1886954598#u32 2005296707#u32 1654813484#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 793247536#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1886954598#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2005296707#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 793247536#u32) (JFs_TX2_RawMath.extend 1886954598#u32) (JFs_TX2_RawMath.extend 2005296707#u32) (JFs_TX2_RawMath.extend 1654813484#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1654813484#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails12.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value0_1=
      ok (.Ok (pack 793247536#u32 1886954598#u32 2005296707#u32 1654813484#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (793247536<2147483647 ∧ 1886954598<2147483647) ∧ (2005296707<2147483647 ∧ 1654813484<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 793247536#u32 1886954598#u32 2005296707#u32 1654813484#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 793247536#u32 1886954598#u32 2005296707#u32 1654813484#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q2_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3384472310#u64 3028433463#u64 7157945013#u64 3965799336#u64⟩,⟨pack 2265226802#u64 2913002714#u64 2939808489#u64 6170857875#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6986516796#u64 4733815673#u64 12228924939#u64 8040188443#u64⟩,⟨pack 6756314610#u64 3755619388#u64 8110694648#u64 7839669824#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7114503012025581743#u64 3262687718514575071#u64 9739141815867555731#u64 6594027107600620804#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1583434021#u32 1407467406#u32 223959870#u32 1219310647#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1583434021#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1407467406#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 223959870#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1219310647#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5295263458981802914#u64 1287064493976726197#u64 9000362958423198006#u64 2390779900762818911#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1583434021#u32 1407467406#u32 223959870#u32 1219310647#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1583434021#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1407467406#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 223959870#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1583434021#u32) (JFs_TX2_RawMath.extend 1407467406#u32) (JFs_TX2_RawMath.extend 223959870#u32) (JFs_TX2_RawMath.extend 1219310647#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1219310647#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails12.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value1_1=
      ok (.Ok (pack 1583434021#u32 1407467406#u32 223959870#u32 1219310647#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1583434021<2147483647 ∧ 1407467406<2147483647) ∧ (223959870<2147483647 ∧ 1219310647<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1583434021#u32 1407467406#u32 223959870#u32 1219310647#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3384472310#u64 3028433463#u64 7157945013#u64 3965799336#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1583434021#u32 1407467406#u32 223959870#u32 1219310647#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2265226802#u64 2913002714#u64 2939808489#u64 6170857875#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6986516796#u64 4733815673#u64 12228924939#u64 8040188443#u64⟩,⟨pack 6756314610#u64 3755619388#u64 8110694648#u64 7839669824#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9422992293#u64 6301978150#u64 17303044898#u64 10189113716#u64⟩,⟨pack 10180085148#u64 6818858686#u64 13741291362#u64 14069440389#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4809745070372314904#u64 1885674635738070143#u64 8920840262341004079#u64 4172625285923321387#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2016803158#u32 1475219222#u32 630263387#u32 2118555418#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2016803158#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1475219222#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 630263387#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2118555418#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5465374079351572001#u64 6345507141326325826#u64 8018028839094489324#u64 11752333239881131940#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2016803158#u32 1475219222#u32 630263387#u32 2118555418#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2016803158#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1475219222#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 630263387#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016803158#u32) (JFs_TX2_RawMath.extend 1475219222#u32) (JFs_TX2_RawMath.extend 630263387#u32) (JFs_TX2_RawMath.extend 2118555418#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2118555418#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails12.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails12.value2_1=
      ok (.Ok (pack 2016803158#u32 1475219222#u32 630263387#u32 2118555418#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2016803158<2147483647 ∧ 1475219222<2147483647) ∧ (630263387<2147483647 ∧ 2118555418<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2016803158#u32 1475219222#u32 630263387#u32 2118555418#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6986516796#u64 4733815673#u64 12228924939#u64 8040188443#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2016803158#u32 1475219222#u32 630263387#u32 2118555418#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6756314610#u64 3755619388#u64 8110694648#u64 7839669824#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q2_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨833057705#u32,2007010856#u32⟩,⟨123175722#u32,1599179128#u32⟩⟩,⟨⟨1590150560#u32,376407745#u32⟩,⟨856389480#u32,1184538507#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q2_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q2_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9422992293%2147483647 at h0
  norm_num at h0
  have e0 : a0=833057705#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6301978150%2147483647 at h1
  norm_num at h1
  have e1 : a1=2007010856#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17303044898%2147483647 at h2
  norm_num at h2
  have e2 : a2=123175722#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10189113716%2147483647 at h3
  norm_num at h3
  have e3 : a3=1599179128#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10180085148%2147483647 at h4
  norm_num at h4
  have e4 : a4=1590150560#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6818858686%2147483647 at h5
  norm_num at h5
  have e5 : a5=376407745#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=13741291362%2147483647 at h6
  norm_num at h6
  have e6 : a6=856389480#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=14069440389%2147483647 at h7
  norm_num at h7
  have e7 : a7=1184538507#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q2_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails12.value0_1
      from JFr_TX2_Tails12.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails12.value1_1
      from JFr_TX2_Tails12.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 2))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails12.value2_1
      from JFr_TX2_Tails12.source2_1,
    JFz_TX2_Q2_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q2_Raw10.after=JFz_TX2_Q2_Raw11.before := rfl
  have same2 : JFz_TX2_Q2_Raw11.after=JFz_TX2_Q2_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q2_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q2_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q2_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1073154022#u32,1360712262#u32⟩,⟨263089029#u32,1489463568#u32⟩⟩,⟨⟨1531961048#u32,1158874901#u32⟩,⟨1340212447#u32,232046220#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1073154022<2147483647 ∧ 1360712262<2147483647) ∧ (263089029<2147483647 ∧ 1489463568<2147483647)) ∧
    ((1531961048<2147483647 ∧ 1158874901<2147483647) ∧ (1340212447<2147483647 ∧ 232046220<2147483647))
  omega
theorem addition : decode JFz_TX2_Q2_Head1.value+decode JFz_TX2_Q2_Tail1.value=decode value := by
  change (⟨⟨⟨240096317,1501185053⟩,⟨139913307,2037768087⟩⟩,⟨⟨2089294135,782467156⟩,⟨483822967,1194991360⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨833057705,2007010856⟩,⟨123175722,1599179128⟩⟩,⟨⟨1590150560,376407745⟩,⟨856389480,1184538507⟩⟩⟩=⟨⟨⟨1073154022,1360712262⟩,⟨263089029,1489463568⟩⟩,⟨⟨1531961048,1158874901⟩,⟨1340212447,232046220⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 2)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 2 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q2_Head1.value JFz_TX2_Q2_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q2_Head1.source,
      JFz_TX2_Q2_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q2_Head1.value := by
    change ((240096317<2147483647 ∧ 1501185053<2147483647) ∧ (139913307<2147483647 ∧ 2037768087<2147483647)) ∧
      ((2089294135<2147483647 ∧ 782467156<2147483647) ∧ (483822967<2147483647 ∧ 1194991360<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q2_Tail1.value := by
    change ((833057705<2147483647 ∧ 2007010856<2147483647) ∧ (123175722<2147483647 ∧ 1599179128<2147483647)) ∧
      ((1590150560<2147483647 ∧ 376407745<2147483647) ∧ (856389480<2147483647 ∧ 1184538507<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q2_Dot1
end
