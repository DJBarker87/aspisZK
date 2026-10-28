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
namespace AspisR1.JFz_TX2_Q11_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨71157560#u32,1578053786#u32⟩,⟨752065218#u32,662958963#u32⟩⟩,⟨⟨2139832734#u32,1564784392#u32⟩,⟨371239041#u32,1979431452#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 11 1 0 0 26%2147483647=71157560 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*767625576+855639275*1357898042+867568255*1972917117+352063*277087355+1106523000*1366763265+1554033304*151445822+1430280692*457969660+1491718280*421556199+118514350*156317770+1675652887*999320608+1364884909*1710255588+1135303194*200300414+304762092*449418426+1465393816*43969155+824208172*144549091+1752653420*125355562+1385409049*398448529+1003904973*1811867511+1298953245*2060922881+2005758375*204062337+497936241*971744729+235809508*1764899410+1478307182*2112510537+1858903615*1844278794+628035096*1324178591+1244951250*1817237767)%2147483647=71157560
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 11 1 1 0 26%2147483647=1578053786 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+1483149559*1357898042+655227887*1972917117+39062738*277087355+729079828*1366763265+67370206*151445822+1685049618*457969660+385547620*421556199+1786803209*156317770+779721715*999320608+594709522*1710255588+338788461*200300414+526756808*449418426+184076238*43969155+1852498770*144549091+2102463508*125355562+1086671526*398448529+1147694576*1811867511+1504805752*2060922881+2005073905*204062337+185008025*971744729+1485990146*1764899410+1255280192*2112510537+1018329259*1844278794+570157693*1324178591+1511904630*1817237767)%2147483647=1578053786
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 11 1 2 0 26%2147483647=752065218 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+1898717401*1357898042+1032732628*1972917117+1313565596*277087355+1074182998*1366763265+1410213748*151445822+1182702806*457969660+321711020*421556199+2062791928*156317770+1188803754*999320608+2038502201*1710255588+735931834*200300414+1330533011*449418426+1052874750*43969155+950153811*144549091+1225424092*125355562+1659116453*398448529+1474177753*1811867511+2073609211*2060922881+1602919019*204062337+1865917845*971744729+1085624123*1764899410+1837870964*2112510537+1550509101*1844278794+1661725734*1324178591+2066655336*1817237767)%2147483647=752065218
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 11 1 3 0 26%2147483647=662958963 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+1849775942*1357898042+656039795*1972917117+1840648083*277087355+246996287*1366763265+1369248953*151445822+1132591724*457969660+92744917*421556199+1719480363*156317770+1266677922*999320608+377386917*1710255588+735227219*200300414+465096431*449418426+451889791*43969155+1379836302*144549091+618598847*125355562+1624084534*398448529+1511477847*1811867511+1840812326*2060922881+185546252*204062337+2145463598*971744729+82870699*1764899410+1625323762*2112510537+1843639311*1844278794+1777269271*1324178591+1645120956*1817237767)%2147483647=662958963
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 11 1 4 0 26%2147483647=2139832734 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+1112406525*1357898042+1345999435*1972917117+752376469*277087355+634588140*1366763265+1419170319*151445822+1702860885*457969660+710076517*421556199+1256487405*156317770+1114745059*999320608+1137838899*1710255588+1254184109*200300414+1038210451*449418426+274378589*43969155+171986381*144549091+1536678585*125355562+1305878831*398448529+1335902916*1811867511+1755193245*2060922881+2023391453*204062337+293456010*971744729+1751078325*1764899410+1423042536*2112510537+1749638204*1844278794+1345811362*1324178591+1284924881*1817237767)%2147483647=2139832734
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 11 1 5 0 26%2147483647=1564784392 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+1796814865*1357898042+1253123171*1972917117+1317611639*277087355+1559245386*1366763265+1866942376*151445822+1973593402*457969660+47019780*421556199+1353487525*156317770+1840161555*999320608+2003659556*1710255588+200559114*200300414+334988447*449418426+2023650872*43969155+1296497964*144549091+34285357*125355562+1685894190*398448529+995962325*1811867511+1295624230*2060922881+1199631211*204062337+1948677857*971744729+1425322328*1764899410+1466877680*2112510537+702011012*1844278794+937706871*1324178591+455802666*1817237767)%2147483647=1564784392
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 11 1 6 0 26%2147483647=371239041 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+1838939499*1357898042+1353876630*1972917117+1258713036*277087355+1947503436*1366763265+1271796599*151445822+1660157177*457969660+564707688*421556199+1858113864*156317770+1015817431*999320608+1264608004*1710255588+735383960*200300414+221696734*449418426+1297524163*43969155+109088572*144549091+792206628*125355562+1921581249*398448529+94118806*1811867511+476103426*2060922881+239612482*204062337+177052717*971744729+826458039*1764899410+1923715623*2112510537+1014161165*1844278794+1341609618*1324178591+786325583*1817237767)%2147483647=371239041
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 11 1 7 0 26%2147483647=1979431452 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*767625576+418714188*1357898042+1675147475*1972917117+1674326661*277087355+547797802*1366763265+2073962627*151445822+897270857*457969660+1582958967*421556199+49892701*156317770+1256824732*999320608+1435903714*1710255588+742583315*200300414+1789294768*449418426+13407412*43969155+518661610*144549091+1259751297*125355562+1695663205*398448529+2068940067*1811867511+940478841*2060922881+1982757556*204062337+1956713516*971744729+863066484*1764899410+522298462*2112510537+1343575777*1844278794+771712139*1324178591+157728743*1817237767)%2147483647=1979431452
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 11 1
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
end AspisR1.JFz_TX2_Q11_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2602343958#u64 2714881462#u64 6622154266#u64 4043331394#u64⟩,⟨pack 2768882715#u64 1018882883#u64 2472514252#u64 5076687870#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 1837172277643229487#u64 4480374274518340706#u64 11496484448046587575#u64 6837580634646931594#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 88284390#u32 2036795440#u32 1994773572#u32 968733029#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 88284390#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2036795440#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1994773572#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 968733029#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2116541762637585682#u64 1020734066173291216#u64 4841669055498514967#u64 7280954230461026663#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 88284390#u32 2036795440#u32 1994773572#u32 968733029#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 88284390#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2036795440#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1994773572#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 88284390#u32) (JFs_TX2_RawMath.extend 2036795440#u32) (JFs_TX2_RawMath.extend 1994773572#u32) (JFs_TX2_RawMath.extend 968733029#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 968733029#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails21.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value0_1=
      ok (.Ok (pack 88284390#u32 2036795440#u32 1994773572#u32 968733029#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (88284390<2147483647 ∧ 2036795440<2147483647) ∧ (1994773572<2147483647 ∧ 968733029<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 88284390#u32 2036795440#u32 1994773572#u32 968733029#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 88284390#u32 2036795440#u32 1994773572#u32 968733029#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q11_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2602343958#u64 2714881462#u64 6622154266#u64 4043331394#u64⟩,⟨pack 2768882715#u64 1018882883#u64 2472514252#u64 5076687870#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5942595258#u64 3775594026#u64 13279406949#u64 7297024014#u64⟩,⟨pack 6497336904#u64 1944389723#u64 7223914612#u64 7354670183#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5880840720329100720#u64 2068106991700699072#u64 10534533873703403471#u64 4629910592259222142#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 843150079#u32 922987750#u32 842063696#u32 960536777#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 843150079#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 922987750#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 842063696#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 960536777#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4934080371916075588#u64 797230943127040629#u64 9397017328784427702#u64 1726814275963027339#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 843150079#u32 922987750#u32 842063696#u32 960536777#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 843150079#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 922987750#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 842063696#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 843150079#u32) (JFs_TX2_RawMath.extend 922987750#u32) (JFs_TX2_RawMath.extend 842063696#u32) (JFs_TX2_RawMath.extend 960536777#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 960536777#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails21.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value1_1=
      ok (.Ok (pack 843150079#u32 922987750#u32 842063696#u32 960536777#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (843150079<2147483647 ∧ 922987750<2147483647) ∧ (842063696<2147483647 ∧ 960536777<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 843150079#u32 922987750#u32 842063696#u32 960536777#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2602343958#u64 2714881462#u64 6622154266#u64 4043331394#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 843150079#u32 922987750#u32 842063696#u32 960536777#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2768882715#u64 1018882883#u64 2472514252#u64 5076687870#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5942595258#u64 3775594026#u64 13279406949#u64 7297024014#u64⟩,⟨pack 6497336904#u64 1944389723#u64 7223914612#u64 7354670183#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9708829328#u64 5958634722#u64 19571413651#u64 9312354701#u64⟩,⟨pack 10389109739#u64 5270340651#u64 13791294408#u64 13736516374#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4698574752444500519#u64 1994432268470535055#u64 9711753429130034843#u64 3838106264833367775#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2024640132#u32 1680027720#u32 961880287#u32 750657856#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2024640132#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1680027720#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 961880287#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750657856#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5100805854914172375#u64 6723526280641279169#u64 10776479440097953132#u64 10387075961766453652#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2024640132#u32 1680027720#u32 961880287#u32 750657856#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2024640132#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1680027720#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 961880287#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2024640132#u32) (JFs_TX2_RawMath.extend 1680027720#u32) (JFs_TX2_RawMath.extend 961880287#u32) (JFs_TX2_RawMath.extend 750657856#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750657856#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails21.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value2_1=
      ok (.Ok (pack 2024640132#u32 1680027720#u32 961880287#u32 750657856#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2024640132<2147483647 ∧ 1680027720<2147483647) ∧ (961880287<2147483647 ∧ 750657856<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2024640132#u32 1680027720#u32 961880287#u32 750657856#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5942595258#u64 3775594026#u64 13279406949#u64 7297024014#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2024640132#u32 1680027720#u32 961880287#u32 750657856#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6497336904#u64 1944389723#u64 7223914612#u64 7354670183#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1118894740#u32,1663667428#u32⟩,⟨244060828#u32,722420113#u32⟩⟩,⟨⟨1799175151#u32,975373357#u32⟩,⟨906392526#u32,851614492#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q11_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q11_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9708829328%2147483647 at h0
  norm_num at h0
  have e0 : a0=1118894740#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5958634722%2147483647 at h1
  norm_num at h1
  have e1 : a1=1663667428#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19571413651%2147483647 at h2
  norm_num at h2
  have e2 : a2=244060828#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9312354701%2147483647 at h3
  norm_num at h3
  have e3 : a3=722420113#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10389109739%2147483647 at h4
  norm_num at h4
  have e4 : a4=1799175151#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5270340651%2147483647 at h5
  norm_num at h5
  have e5 : a5=975373357#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=13791294408%2147483647 at h6
  norm_num at h6
  have e6 : a6=906392526#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=13736516374%2147483647 at h7
  norm_num at h7
  have e7 : a7=851614492#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q11_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails21.value0_1
      from JFr_TX2_Tails21.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails21.value1_1
      from JFr_TX2_Tails21.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails21.value2_1
      from JFr_TX2_Tails21.source2_1,
    JFz_TX2_Q11_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q11_Raw10.after=JFz_TX2_Q11_Raw11.before := rfl
  have same2 : JFz_TX2_Q11_Raw11.after=JFz_TX2_Q11_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q11_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q11_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q11_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1190052300#u32,1094237567#u32⟩,⟨996126046#u32,1385379076#u32⟩⟩,⟨⟨1791524238#u32,392674102#u32⟩,⟨1277631567#u32,683562297#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1190052300<2147483647 ∧ 1094237567<2147483647) ∧ (996126046<2147483647 ∧ 1385379076<2147483647)) ∧
    ((1791524238<2147483647 ∧ 392674102<2147483647) ∧ (1277631567<2147483647 ∧ 683562297<2147483647))
  omega
theorem addition : decode JFz_TX2_Q11_Head1.value+decode JFz_TX2_Q11_Tail1.value=decode value := by
  change (⟨⟨⟨71157560,1578053786⟩,⟨752065218,662958963⟩⟩,⟨⟨2139832734,1564784392⟩,⟨371239041,1979431452⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1118894740,1663667428⟩,⟨244060828,722420113⟩⟩,⟨⟨1799175151,975373357⟩,⟨906392526,851614492⟩⟩⟩=⟨⟨⟨1190052300,1094237567⟩,⟨996126046,1385379076⟩⟩,⟨⟨1791524238,392674102⟩,⟨1277631567,683562297⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 11 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q11_Head1.value JFz_TX2_Q11_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q11_Head1.source,
      JFz_TX2_Q11_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q11_Head1.value := by
    change ((71157560<2147483647 ∧ 1578053786<2147483647) ∧ (752065218<2147483647 ∧ 662958963<2147483647)) ∧
      ((2139832734<2147483647 ∧ 1564784392<2147483647) ∧ (371239041<2147483647 ∧ 1979431452<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q11_Tail1.value := by
    change ((1118894740<2147483647 ∧ 1663667428<2147483647) ∧ (244060828<2147483647 ∧ 722420113<2147483647)) ∧
      ((1799175151<2147483647 ∧ 975373357<2147483647) ∧ (906392526<2147483647 ∧ 851614492<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q11_Dot1
end
