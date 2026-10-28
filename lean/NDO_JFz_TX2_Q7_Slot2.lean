import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails17
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1368486920#u32,2007834467#u32⟩,⟨1753870528#u32,568804845#u32⟩⟩,⟨⟨1815982559#u32,1836391534#u32⟩,⟨745068906#u32,327313573#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 7 2 0 0 26%2147483647=1368486920 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1624459960+855639275*1857981794+867568255*545340763+352063*2047024007+1106523000*1877970918+1554033304*1701431859+1430280692*33715990+1491718280*296868384+118514350*1858404617+1675652887*173447136+1364884909*774258356+1135303194*1345200268+304762092*359376471+1465393816*1783706145+824208172*399733817+1752653420*1157757315+1385409049*353990606+1003904973*992378381+1298953245*1183839743+2005758375*955868943+497936241*1908666067+235809508*1990787020+1478307182*1797423075+1858903615*921495673+628035096*43546838+1244951250*2064908811)%2147483647=1368486920
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 7 2 1 0 26%2147483647=2007834467 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+1483149559*1857981794+655227887*545340763+39062738*2047024007+729079828*1877970918+67370206*1701431859+1685049618*33715990+385547620*296868384+1786803209*1858404617+779721715*173447136+594709522*774258356+338788461*1345200268+526756808*359376471+184076238*1783706145+1852498770*399733817+2102463508*1157757315+1086671526*353990606+1147694576*992378381+1504805752*1183839743+2005073905*955868943+185008025*1908666067+1485990146*1990787020+1255280192*1797423075+1018329259*921495673+570157693*43546838+1511904630*2064908811)%2147483647=2007834467
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 7 2 2 0 26%2147483647=1753870528 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+1898717401*1857981794+1032732628*545340763+1313565596*2047024007+1074182998*1877970918+1410213748*1701431859+1182702806*33715990+321711020*296868384+2062791928*1858404617+1188803754*173447136+2038502201*774258356+735931834*1345200268+1330533011*359376471+1052874750*1783706145+950153811*399733817+1225424092*1157757315+1659116453*353990606+1474177753*992378381+2073609211*1183839743+1602919019*955868943+1865917845*1908666067+1085624123*1990787020+1837870964*1797423075+1550509101*921495673+1661725734*43546838+2066655336*2064908811)%2147483647=1753870528
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 7 2 3 0 26%2147483647=568804845 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+1849775942*1857981794+656039795*545340763+1840648083*2047024007+246996287*1877970918+1369248953*1701431859+1132591724*33715990+92744917*296868384+1719480363*1858404617+1266677922*173447136+377386917*774258356+735227219*1345200268+465096431*359376471+451889791*1783706145+1379836302*399733817+618598847*1157757315+1624084534*353990606+1511477847*992378381+1840812326*1183839743+185546252*955868943+2145463598*1908666067+82870699*1990787020+1625323762*1797423075+1843639311*921495673+1777269271*43546838+1645120956*2064908811)%2147483647=568804845
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 7 2 4 0 26%2147483647=1815982559 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+1112406525*1857981794+1345999435*545340763+752376469*2047024007+634588140*1877970918+1419170319*1701431859+1702860885*33715990+710076517*296868384+1256487405*1858404617+1114745059*173447136+1137838899*774258356+1254184109*1345200268+1038210451*359376471+274378589*1783706145+171986381*399733817+1536678585*1157757315+1305878831*353990606+1335902916*992378381+1755193245*1183839743+2023391453*955868943+293456010*1908666067+1751078325*1990787020+1423042536*1797423075+1749638204*921495673+1345811362*43546838+1284924881*2064908811)%2147483647=1815982559
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 7 2 5 0 26%2147483647=1836391534 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+1796814865*1857981794+1253123171*545340763+1317611639*2047024007+1559245386*1877970918+1866942376*1701431859+1973593402*33715990+47019780*296868384+1353487525*1858404617+1840161555*173447136+2003659556*774258356+200559114*1345200268+334988447*359376471+2023650872*1783706145+1296497964*399733817+34285357*1157757315+1685894190*353990606+995962325*992378381+1295624230*1183839743+1199631211*955868943+1948677857*1908666067+1425322328*1990787020+1466877680*1797423075+702011012*921495673+937706871*43546838+455802666*2064908811)%2147483647=1836391534
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 7 2 6 0 26%2147483647=745068906 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+1838939499*1857981794+1353876630*545340763+1258713036*2047024007+1947503436*1877970918+1271796599*1701431859+1660157177*33715990+564707688*296868384+1858113864*1858404617+1015817431*173447136+1264608004*774258356+735383960*1345200268+221696734*359376471+1297524163*1783706145+109088572*399733817+792206628*1157757315+1921581249*353990606+94118806*992378381+476103426*1183839743+239612482*955868943+177052717*1908666067+826458039*1990787020+1923715623*1797423075+1014161165*921495673+1341609618*43546838+786325583*2064908811)%2147483647=745068906
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 7 2 7 0 26%2147483647=327313573 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1624459960+418714188*1857981794+1675147475*545340763+1674326661*2047024007+547797802*1877970918+2073962627*1701431859+897270857*33715990+1582958967*296868384+49892701*1858404617+1256824732*173447136+1435903714*774258356+742583315*1345200268+1789294768*359376471+13407412*1783706145+518661610*399733817+1259751297*1157757315+1695663205*353990606+2068940067*992378381+940478841*1183839743+1982757556*955868943+1956713516*1908666067+863066484*1990787020+522298462*1797423075+1343575777*921495673+771712139*43546838+157728743*2064908811)%2147483647=327313573
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 7 2
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
end AspisR1.JFz_TX2_Q7_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4070420786#u64 4826902176#u64 6508255259#u64 4134596700#u64⟩,⟨pack 2926225777#u64 2377140349#u64 4749615483#u64 5072471596#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 5657091490037998521#u64 7289247028224423814#u64 11485318920242724530#u64 6598862983135834757#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1921364423#u32 2103297525#u32 1275140936#u32 1041194587#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1921364423#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2103297525#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1275140936#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1041194587#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2853553503290716636#u64 3331592878063871065#u64 8053931627317739826#u64 10378833576769993184#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1921364423#u32 2103297525#u32 1275140936#u32 1041194587#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1921364423#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2103297525#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1275140936#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1921364423#u32) (JFs_TX2_RawMath.extend 2103297525#u32) (JFs_TX2_RawMath.extend 1275140936#u32) (JFs_TX2_RawMath.extend 1041194587#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1041194587#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails17.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value0_2=
      ok (.Ok (pack 1921364423#u32 2103297525#u32 1275140936#u32 1041194587#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1921364423<2147483647 ∧ 2103297525<2147483647) ∧ (1275140936<2147483647 ∧ 1041194587<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1921364423#u32 2103297525#u32 1275140936#u32 1041194587#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1921364423#u32 2103297525#u32 1275140936#u32 1041194587#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q7_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4070420786#u64 4826902176#u64 6508255259#u64 4134596700#u64⟩,⟨pack 2926225777#u64 2377140349#u64 4749615483#u64 5072471596#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7495386615#u64 7247297196#u64 13202320962#u64 8727878417#u64⟩,⟨pack 7021649595#u64 4029525238#u64 9607259020#u64 8009831076#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5591765234419299088#u64 2261669907596716660#u64 12504316057859576767#u64 5889496085701887933#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 715707969#u32 1049019171#u32 2139286122#u32 1360355906#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 715707969#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1049019171#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2139286122#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1360355906#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4821697901585955815#u64 847943944123999085#u64 10007062682907790614#u64 2280785308595689514#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 715707969#u32 1049019171#u32 2139286122#u32 1360355906#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 715707969#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1049019171#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2139286122#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 715707969#u32) (JFs_TX2_RawMath.extend 1049019171#u32) (JFs_TX2_RawMath.extend 2139286122#u32) (JFs_TX2_RawMath.extend 1360355906#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1360355906#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails17.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value1_2=
      ok (.Ok (pack 715707969#u32 1049019171#u32 2139286122#u32 1360355906#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (715707969<2147483647 ∧ 1049019171<2147483647) ∧ (2139286122<2147483647 ∧ 1360355906<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 715707969#u32 1049019171#u32 2139286122#u32 1360355906#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4070420786#u64 4826902176#u64 6508255259#u64 4134596700#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 715707969#u32 1049019171#u32 2139286122#u32 1360355906#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2926225777#u64 2377140349#u64 4749615483#u64 5072471596#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7495386615#u64 7247297196#u64 13202320962#u64 8727878417#u64⟩,⟨pack 7021649595#u64 4029525238#u64 9607259020#u64 8009831076#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9633440820#u64 9220605087#u64 17240735604#u64 9593816917#u64⟩,⟨pack 8405406579#u64 5723522972#u64 14629382057#u64 10344805660#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4013289266389711767#u64 855131585096332969#u64 8505516713522101356#u64 1591422238130794516#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 305592727#u32 1341101155#u32 273454876#u32 185640119#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 305592727#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1341101155#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 273454876#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 185640119#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2675807646085657335#u64 2945189695882626509#u64 7562331406285794156#u64 4246348219322254350#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 305592727#u32 1341101155#u32 273454876#u32 185640119#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 305592727#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1341101155#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 273454876#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 305592727#u32) (JFs_TX2_RawMath.extend 1341101155#u32) (JFs_TX2_RawMath.extend 273454876#u32) (JFs_TX2_RawMath.extend 185640119#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 185640119#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails17.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value2_2=
      ok (.Ok (pack 305592727#u32 1341101155#u32 273454876#u32 185640119#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (305592727<2147483647 ∧ 1341101155<2147483647) ∧ (273454876<2147483647 ∧ 185640119<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 305592727#u32 1341101155#u32 273454876#u32 185640119#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7495386615#u64 7247297196#u64 13202320962#u64 8727878417#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 305592727#u32 1341101155#u32 273454876#u32 185640119#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7021649595#u64 4029525238#u64 9607259020#u64 8009831076#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1043506232#u32,630670499#u32⟩,⟨60866428#u32,1003882329#u32⟩⟩,⟨⟨1962955638#u32,1428555678#u32⟩,⟨1744480175#u32,1754871072#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q7_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q7_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9633440820%2147483647 at h0
  norm_num at h0
  have e0 : a0=1043506232#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=9220605087%2147483647 at h1
  norm_num at h1
  have e1 : a1=630670499#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17240735604%2147483647 at h2
  norm_num at h2
  have e2 : a2=60866428#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9593816917%2147483647 at h3
  norm_num at h3
  have e3 : a3=1003882329#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8405406579%2147483647 at h4
  norm_num at h4
  have e4 : a4=1962955638#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5723522972%2147483647 at h5
  norm_num at h5
  have e5 : a5=1428555678#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14629382057%2147483647 at h6
  norm_num at h6
  have e6 : a6=1744480175#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10344805660%2147483647 at h7
  norm_num at h7
  have e7 : a7=1754871072#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q7_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails17.value0_2
      from JFr_TX2_Tails17.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails17.value1_2
      from JFr_TX2_Tails17.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails17.value2_2
      from JFr_TX2_Tails17.source2_2,
    JFz_TX2_Q7_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q7_Raw20.after=JFz_TX2_Q7_Raw21.before := rfl
  have same2 : JFz_TX2_Q7_Raw21.after=JFz_TX2_Q7_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q7_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q7_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q7_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨264509505#u32,491021319#u32⟩,⟨1814736956#u32,1572687174#u32⟩⟩,⟨⟨1631454550#u32,1117463565#u32⟩,⟨342065434#u32,2082184645#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((264509505<2147483647 ∧ 491021319<2147483647) ∧ (1814736956<2147483647 ∧ 1572687174<2147483647)) ∧
    ((1631454550<2147483647 ∧ 1117463565<2147483647) ∧ (342065434<2147483647 ∧ 2082184645<2147483647))
  omega
theorem addition : decode JFz_TX2_Q7_Head2.value+decode JFz_TX2_Q7_Tail2.value=decode value := by
  change (⟨⟨⟨1368486920,2007834467⟩,⟨1753870528,568804845⟩⟩,⟨⟨1815982559,1836391534⟩,⟨745068906,327313573⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1043506232,630670499⟩,⟨60866428,1003882329⟩⟩,⟨⟨1962955638,1428555678⟩,⟨1744480175,1754871072⟩⟩⟩=⟨⟨⟨264509505,491021319⟩,⟨1814736956,1572687174⟩⟩,⟨⟨1631454550,1117463565⟩,⟨342065434,2082184645⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 7 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q7_Head2.value JFz_TX2_Q7_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q7_Head2.source,
      JFz_TX2_Q7_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q7_Head2.value := by
    change ((1368486920<2147483647 ∧ 2007834467<2147483647) ∧ (1753870528<2147483647 ∧ 568804845<2147483647)) ∧
      ((1815982559<2147483647 ∧ 1836391534<2147483647) ∧ (745068906<2147483647 ∧ 327313573<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q7_Tail2.value := by
    change ((1043506232<2147483647 ∧ 630670499<2147483647) ∧ (60866428<2147483647 ∧ 1003882329<2147483647)) ∧
      ((1962955638<2147483647 ∧ 1428555678<2147483647) ∧ (1744480175<2147483647 ∧ 1754871072<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q7_Dot2
end
