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
namespace AspisR1.JFz_TX2_Q10_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1802223725#u32,1030731588#u32⟩,⟨925629292#u32,1063391994#u32⟩⟩,⟨⟨1525761089#u32,1736262433#u32⟩,⟨303505455#u32,662408099#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 10 2 0 0 26%2147483647=1802223725 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*452680207+855639275*60722363+867568255*2098899933+352063*888848230+1106523000*1771912613+1554033304*673774274+1430280692*1965636403+1491718280*2572424+118514350*1682967798+1675652887*156488049+1364884909*2084741710+1135303194*226089952+304762092*305624092+1465393816*892525047+824208172*1901599362+1752653420*74799771+1385409049*1642597993+1003904973*655933323+1298953245*264949572+2005758375*300197812+497936241*436391685+235809508*1975815058+1478307182*604156269+1858903615*1338946867+628035096*2146850300+1244951250*943006445)%2147483647=1802223725
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 10 2 1 0 26%2147483647=1030731588 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+1483149559*60722363+655227887*2098899933+39062738*888848230+729079828*1771912613+67370206*673774274+1685049618*1965636403+385547620*2572424+1786803209*1682967798+779721715*156488049+594709522*2084741710+338788461*226089952+526756808*305624092+184076238*892525047+1852498770*1901599362+2102463508*74799771+1086671526*1642597993+1147694576*655933323+1504805752*264949572+2005073905*300197812+185008025*436391685+1485990146*1975815058+1255280192*604156269+1018329259*1338946867+570157693*2146850300+1511904630*943006445)%2147483647=1030731588
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 10 2 2 0 26%2147483647=925629292 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+1898717401*60722363+1032732628*2098899933+1313565596*888848230+1074182998*1771912613+1410213748*673774274+1182702806*1965636403+321711020*2572424+2062791928*1682967798+1188803754*156488049+2038502201*2084741710+735931834*226089952+1330533011*305624092+1052874750*892525047+950153811*1901599362+1225424092*74799771+1659116453*1642597993+1474177753*655933323+2073609211*264949572+1602919019*300197812+1865917845*436391685+1085624123*1975815058+1837870964*604156269+1550509101*1338946867+1661725734*2146850300+2066655336*943006445)%2147483647=925629292
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 10 2 3 0 26%2147483647=1063391994 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+1849775942*60722363+656039795*2098899933+1840648083*888848230+246996287*1771912613+1369248953*673774274+1132591724*1965636403+92744917*2572424+1719480363*1682967798+1266677922*156488049+377386917*2084741710+735227219*226089952+465096431*305624092+451889791*892525047+1379836302*1901599362+618598847*74799771+1624084534*1642597993+1511477847*655933323+1840812326*264949572+185546252*300197812+2145463598*436391685+82870699*1975815058+1625323762*604156269+1843639311*1338946867+1777269271*2146850300+1645120956*943006445)%2147483647=1063391994
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 10 2 4 0 26%2147483647=1525761089 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+1112406525*60722363+1345999435*2098899933+752376469*888848230+634588140*1771912613+1419170319*673774274+1702860885*1965636403+710076517*2572424+1256487405*1682967798+1114745059*156488049+1137838899*2084741710+1254184109*226089952+1038210451*305624092+274378589*892525047+171986381*1901599362+1536678585*74799771+1305878831*1642597993+1335902916*655933323+1755193245*264949572+2023391453*300197812+293456010*436391685+1751078325*1975815058+1423042536*604156269+1749638204*1338946867+1345811362*2146850300+1284924881*943006445)%2147483647=1525761089
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 10 2 5 0 26%2147483647=1736262433 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+1796814865*60722363+1253123171*2098899933+1317611639*888848230+1559245386*1771912613+1866942376*673774274+1973593402*1965636403+47019780*2572424+1353487525*1682967798+1840161555*156488049+2003659556*2084741710+200559114*226089952+334988447*305624092+2023650872*892525047+1296497964*1901599362+34285357*74799771+1685894190*1642597993+995962325*655933323+1295624230*264949572+1199631211*300197812+1948677857*436391685+1425322328*1975815058+1466877680*604156269+702011012*1338946867+937706871*2146850300+455802666*943006445)%2147483647=1736262433
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 10 2 6 0 26%2147483647=303505455 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+1838939499*60722363+1353876630*2098899933+1258713036*888848230+1947503436*1771912613+1271796599*673774274+1660157177*1965636403+564707688*2572424+1858113864*1682967798+1015817431*156488049+1264608004*2084741710+735383960*226089952+221696734*305624092+1297524163*892525047+109088572*1901599362+792206628*74799771+1921581249*1642597993+94118806*655933323+476103426*264949572+239612482*300197812+177052717*436391685+826458039*1975815058+1923715623*604156269+1014161165*1338946867+1341609618*2146850300+786325583*943006445)%2147483647=303505455
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 10 2 7 0 26%2147483647=662408099 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*452680207+418714188*60722363+1675147475*2098899933+1674326661*888848230+547797802*1771912613+2073962627*673774274+897270857*1965636403+1582958967*2572424+49892701*1682967798+1256824732*156488049+1435903714*2084741710+742583315*226089952+1789294768*305624092+13407412*892525047+518661610*1901599362+1259751297*74799771+1695663205*1642597993+2068940067*655933323+940478841*264949572+1982757556*300197812+1956713516*436391685+863066484*1975815058+522298462*604156269+1343575777*1338946867+771712139*2146850300+157728743*943006445)%2147483647=662408099
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 10 2
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
end AspisR1.JFz_TX2_Q10_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4306714440#u64 3606162341#u64 5702892369#u64 4125699769#u64⟩,⟨pack 1872945437#u64 2796744952#u64 5473228871#u64 3992891053#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5938411719182273355#u64 4200923656502136840#u64 9352287813759351523#u64 7209046918558765765#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1338909753#u32 1054480979#u32 1032357434#u32 2023074862#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1338909753#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1054480979#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1032357434#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2023074862#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3898241699502109893#u64 2137736352519514419#u64 7716022174935496117#u64 7147553110013789007#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1338909753#u32 1054480979#u32 1032357434#u32 2023074862#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1338909753#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1054480979#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1032357434#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1338909753#u32) (JFs_TX2_RawMath.extend 1054480979#u32) (JFs_TX2_RawMath.extend 1032357434#u32) (JFs_TX2_RawMath.extend 2023074862#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2023074862#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails20.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value0_2=
      ok (.Ok (pack 1338909753#u32 1054480979#u32 1032357434#u32 2023074862#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1338909753<2147483647 ∧ 1054480979<2147483647) ∧ (1032357434<2147483647 ∧ 2023074862<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1338909753#u32 1054480979#u32 1032357434#u32 2023074862#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1338909753#u32 1054480979#u32 1032357434#u32 2023074862#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q10_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4306714440#u64 3606162341#u64 5702892369#u64 4125699769#u64⟩,⟨pack 1872945437#u64 2796744952#u64 5473228871#u64 3992891053#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7339362805#u64 5712685403#u64 12361689731#u64 7049515213#u64⟩,⟨pack 5462895519#u64 5249789143#u64 10292526496#u64 5100942354#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5891576766014447352#u64 1716116343338385477#u64 11474089180794773648#u64 4724028553147425843#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 814367609#u32 743855546#u32 1259584155#u32 1090640713#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 814367609#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 743855546#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1259584155#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1090640713#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4958461735021989160#u64 674831399047103670#u64 9724035973261244148#u64 1811985789073004146#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 814367609#u32 743855546#u32 1259584155#u32 1090640713#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 814367609#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 743855546#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1259584155#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 814367609#u32) (JFs_TX2_RawMath.extend 743855546#u32) (JFs_TX2_RawMath.extend 1259584155#u32) (JFs_TX2_RawMath.extend 1090640713#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1090640713#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails20.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value1_2=
      ok (.Ok (pack 814367609#u32 743855546#u32 1259584155#u32 1090640713#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (814367609<2147483647 ∧ 743855546<2147483647) ∧ (1259584155<2147483647 ∧ 1090640713<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 814367609#u32 743855546#u32 1259584155#u32 1090640713#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4306714440#u64 3606162341#u64 5702892369#u64 4125699769#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 814367609#u32 743855546#u32 1259584155#u32 1090640713#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1872945437#u64 2796744952#u64 5473228871#u64 3992891053#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7339362805#u64 5712685403#u64 12361689731#u64 7049515213#u64⟩,⟨pack 5462895519#u64 5249789143#u64 10292526496#u64 5100942354#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10127689584#u64 6494581804#u64 17425942969#u64 9592882336#u64⟩,⟨pack 8170715518#u64 7563061038#u64 14993167071#u64 10503335076#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4665102510123839859#u64 1131852302272987001#u64 8625487108258306448#u64 2710741500317907395#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1152629403#u32 949415336#u32 286924247#u32 1758281081#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1152629403#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 949415336#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 286924247#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1758281081#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4903126021916540824#u64 3815238351724532789#u64 7198196496014234137#u64 7779122088443902957#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1152629403#u32 949415336#u32 286924247#u32 1758281081#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1152629403#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 949415336#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 286924247#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1152629403#u32) (JFs_TX2_RawMath.extend 949415336#u32) (JFs_TX2_RawMath.extend 286924247#u32) (JFs_TX2_RawMath.extend 1758281081#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1758281081#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails20.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails20.value2_2=
      ok (.Ok (pack 1152629403#u32 949415336#u32 286924247#u32 1758281081#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1152629403<2147483647 ∧ 949415336<2147483647) ∧ (286924247<2147483647 ∧ 1758281081<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1152629403#u32 949415336#u32 286924247#u32 1758281081#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7339362805#u64 5712685403#u64 12361689731#u64 7049515213#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1152629403#u32 949415336#u32 286924247#u32 1758281081#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5462895519#u64 5249789143#u64 10292526496#u64 5100942354#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q10_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1537754996#u32,52130863#u32⟩,⟨246073793#u32,1002947748#u32⟩⟩,⟨⟨1728264577#u32,1120610097#u32⟩,⟨2108265189#u32,1913400488#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q10_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q10_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10127689584%2147483647 at h0
  norm_num at h0
  have e0 : a0=1537754996#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6494581804%2147483647 at h1
  norm_num at h1
  have e1 : a1=52130863#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17425942969%2147483647 at h2
  norm_num at h2
  have e2 : a2=246073793#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9592882336%2147483647 at h3
  norm_num at h3
  have e3 : a3=1002947748#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8170715518%2147483647 at h4
  norm_num at h4
  have e4 : a4=1728264577#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7563061038%2147483647 at h5
  norm_num at h5
  have e5 : a5=1120610097#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14993167071%2147483647 at h6
  norm_num at h6
  have e6 : a6=2108265189#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10503335076%2147483647 at h7
  norm_num at h7
  have e7 : a7=1913400488#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q10_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails20.value0_2
      from JFr_TX2_Tails20.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails20.value1_2
      from JFr_TX2_Tails20.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 10))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails20.value2_2
      from JFr_TX2_Tails20.source2_2,
    JFz_TX2_Q10_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q10_Raw20.after=JFz_TX2_Q10_Raw21.before := rfl
  have same2 : JFz_TX2_Q10_Raw21.after=JFz_TX2_Q10_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q10_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q10_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q10_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1192495074#u32,1082862451#u32⟩,⟨1171703085#u32,2066339742#u32⟩⟩,⟨⟨1106542019#u32,709388883#u32⟩,⟨264286997#u32,428324940#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1192495074<2147483647 ∧ 1082862451<2147483647) ∧ (1171703085<2147483647 ∧ 2066339742<2147483647)) ∧
    ((1106542019<2147483647 ∧ 709388883<2147483647) ∧ (264286997<2147483647 ∧ 428324940<2147483647))
  omega
theorem addition : decode JFz_TX2_Q10_Head2.value+decode JFz_TX2_Q10_Tail2.value=decode value := by
  change (⟨⟨⟨1802223725,1030731588⟩,⟨925629292,1063391994⟩⟩,⟨⟨1525761089,1736262433⟩,⟨303505455,662408099⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1537754996,52130863⟩,⟨246073793,1002947748⟩⟩,⟨⟨1728264577,1120610097⟩,⟨2108265189,1913400488⟩⟩⟩=⟨⟨⟨1192495074,1082862451⟩,⟨1171703085,2066339742⟩⟩,⟨⟨1106542019,709388883⟩,⟨264286997,428324940⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 10)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 10 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q10_Head2.value JFz_TX2_Q10_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q10_Head2.source,
      JFz_TX2_Q10_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q10_Head2.value := by
    change ((1802223725<2147483647 ∧ 1030731588<2147483647) ∧ (925629292<2147483647 ∧ 1063391994<2147483647)) ∧
      ((1525761089<2147483647 ∧ 1736262433<2147483647) ∧ (303505455<2147483647 ∧ 662408099<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q10_Tail2.value := by
    change ((1537754996<2147483647 ∧ 52130863<2147483647) ∧ (246073793<2147483647 ∧ 1002947748<2147483647)) ∧
      ((1728264577<2147483647 ∧ 1120610097<2147483647) ∧ (2108265189<2147483647 ∧ 1913400488<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q10_Dot2
end
