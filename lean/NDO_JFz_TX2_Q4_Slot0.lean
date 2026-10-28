import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails14
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1456829136#u32,371876612#u32⟩,⟨1945492646#u32,1371255559#u32⟩⟩,⟨⟨1541532099#u32,671063478#u32⟩,⟨2107332907#u32,400154539#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 4 0 0 0 26%2147483647=1456829136 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1492509364+855639275*592067641+867568255*1568896681+352063*1740411835+1106523000*684748144+1554033304*874114293+1430280692*2104780172+1491718280*628675680+118514350*1176901081+1675652887*1450814267+1364884909*1962021055+1135303194*2042816151+304762092*618032172+1465393816*1379868153+824208172*1250941710+1752653420*350271933+1385409049*126320101+1003904973*642872245+1298953245*924733205+2005758375*988642436+497936241*1660224438+235809508*1282701173+1478307182*1609332963+1858903615*275965647+628035096*730968355+1244951250*486799743)%2147483647=1456829136
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 4 0 1 0 26%2147483647=371876612 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+1483149559*592067641+655227887*1568896681+39062738*1740411835+729079828*684748144+67370206*874114293+1685049618*2104780172+385547620*628675680+1786803209*1176901081+779721715*1450814267+594709522*1962021055+338788461*2042816151+526756808*618032172+184076238*1379868153+1852498770*1250941710+2102463508*350271933+1086671526*126320101+1147694576*642872245+1504805752*924733205+2005073905*988642436+185008025*1660224438+1485990146*1282701173+1255280192*1609332963+1018329259*275965647+570157693*730968355+1511904630*486799743)%2147483647=371876612
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 4 0 2 0 26%2147483647=1945492646 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+1898717401*592067641+1032732628*1568896681+1313565596*1740411835+1074182998*684748144+1410213748*874114293+1182702806*2104780172+321711020*628675680+2062791928*1176901081+1188803754*1450814267+2038502201*1962021055+735931834*2042816151+1330533011*618032172+1052874750*1379868153+950153811*1250941710+1225424092*350271933+1659116453*126320101+1474177753*642872245+2073609211*924733205+1602919019*988642436+1865917845*1660224438+1085624123*1282701173+1837870964*1609332963+1550509101*275965647+1661725734*730968355+2066655336*486799743)%2147483647=1945492646
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 4 0 3 0 26%2147483647=1371255559 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+1849775942*592067641+656039795*1568896681+1840648083*1740411835+246996287*684748144+1369248953*874114293+1132591724*2104780172+92744917*628675680+1719480363*1176901081+1266677922*1450814267+377386917*1962021055+735227219*2042816151+465096431*618032172+451889791*1379868153+1379836302*1250941710+618598847*350271933+1624084534*126320101+1511477847*642872245+1840812326*924733205+185546252*988642436+2145463598*1660224438+82870699*1282701173+1625323762*1609332963+1843639311*275965647+1777269271*730968355+1645120956*486799743)%2147483647=1371255559
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 4 0 4 0 26%2147483647=1541532099 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+1112406525*592067641+1345999435*1568896681+752376469*1740411835+634588140*684748144+1419170319*874114293+1702860885*2104780172+710076517*628675680+1256487405*1176901081+1114745059*1450814267+1137838899*1962021055+1254184109*2042816151+1038210451*618032172+274378589*1379868153+171986381*1250941710+1536678585*350271933+1305878831*126320101+1335902916*642872245+1755193245*924733205+2023391453*988642436+293456010*1660224438+1751078325*1282701173+1423042536*1609332963+1749638204*275965647+1345811362*730968355+1284924881*486799743)%2147483647=1541532099
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 4 0 5 0 26%2147483647=671063478 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+1796814865*592067641+1253123171*1568896681+1317611639*1740411835+1559245386*684748144+1866942376*874114293+1973593402*2104780172+47019780*628675680+1353487525*1176901081+1840161555*1450814267+2003659556*1962021055+200559114*2042816151+334988447*618032172+2023650872*1379868153+1296497964*1250941710+34285357*350271933+1685894190*126320101+995962325*642872245+1295624230*924733205+1199631211*988642436+1948677857*1660224438+1425322328*1282701173+1466877680*1609332963+702011012*275965647+937706871*730968355+455802666*486799743)%2147483647=671063478
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 4 0 6 0 26%2147483647=2107332907 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+1838939499*592067641+1353876630*1568896681+1258713036*1740411835+1947503436*684748144+1271796599*874114293+1660157177*2104780172+564707688*628675680+1858113864*1176901081+1015817431*1450814267+1264608004*1962021055+735383960*2042816151+221696734*618032172+1297524163*1379868153+109088572*1250941710+792206628*350271933+1921581249*126320101+94118806*642872245+476103426*924733205+239612482*988642436+177052717*1660224438+826458039*1282701173+1923715623*1609332963+1014161165*275965647+1341609618*730968355+786325583*486799743)%2147483647=2107332907
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 4 0 7 0 26%2147483647=400154539 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1492509364+418714188*592067641+1675147475*1568896681+1674326661*1740411835+547797802*684748144+2073962627*874114293+897270857*2104780172+1582958967*628675680+49892701*1176901081+1256824732*1450814267+1435903714*1962021055+742583315*2042816151+1789294768*618032172+13407412*1379868153+518661610*1250941710+1259751297*350271933+1695663205*126320101+2068940067*642872245+940478841*924733205+1982757556*988642436+1956713516*1660224438+863066484*1282701173+522298462*1609332963+1343575777*275965647+771712139*730968355+157728743*486799743)%2147483647=400154539
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 4 0
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
end AspisR1.JFz_TX2_Q4_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 1673151903#u64 3860683592#u64 4874244932#u64 3953954460#u64⟩,⟨pack 1537853225#u64 819940076#u64 2197884609#u64 3842624034#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 2764836243148434891#u64 4530561455973320705#u64 8965870672788896645#u64 7672332065294605282#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 395854293#u32 1850865851#u32 1274174721#u32 1881944900#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 395854293#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1850865851#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1274174721#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1881944900#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2485463700168605447#u64 1320330503852246970#u64 4402301258326659946#u64 7052645074379324282#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 395854293#u32 1850865851#u32 1274174721#u32 1881944900#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 395854293#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1850865851#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1274174721#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 395854293#u32) (JFs_TX2_RawMath.extend 1850865851#u32) (JFs_TX2_RawMath.extend 1274174721#u32) (JFs_TX2_RawMath.extend 1881944900#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1881944900#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails14.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value0_0=
      ok (.Ok (pack 395854293#u32 1850865851#u32 1274174721#u32 1881944900#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (395854293<2147483647 ∧ 1850865851<2147483647) ∧ (1274174721<2147483647 ∧ 1881944900<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 395854293#u32 1850865851#u32 1274174721#u32 1881944900#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 395854293#u32 1850865851#u32 1274174721#u32 1881944900#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q4_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 1673151903#u64 3860683592#u64 4874244932#u64 3953954460#u64⟩,⟨pack 1537853225#u64 819940076#u64 2197884609#u64 3842624034#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5325960299#u64 4946082991#u64 13116530384#u64 8639255073#u64⟩,⟨pack 6254209886#u64 2289188996#u64 8121659814#u64 6426177256#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7829413306143742709#u64 1695591584824949319#u64 13615239895808291444#u64 6844940302265338277#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1792815254#u32 545108715#u32 1578207495#u32 1626509108#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1792815254#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 545108715#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1578207495#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1626509108#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5636982595547347098#u64 781226972115370499#u64 10364387193134922859#u64 2700903229231125100#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1792815254#u32 545108715#u32 1578207495#u32 1626509108#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1792815254#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 545108715#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1578207495#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1792815254#u32) (JFs_TX2_RawMath.extend 545108715#u32) (JFs_TX2_RawMath.extend 1578207495#u32) (JFs_TX2_RawMath.extend 1626509108#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1626509108#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails14.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value1_0=
      ok (.Ok (pack 1792815254#u32 545108715#u32 1578207495#u32 1626509108#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1792815254<2147483647 ∧ 545108715<2147483647) ∧ (1578207495<2147483647 ∧ 1626509108<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1792815254#u32 545108715#u32 1578207495#u32 1626509108#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1673151903#u64 3860683592#u64 4874244932#u64 3953954460#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1792815254#u32 545108715#u32 1578207495#u32 1626509108#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1537853225#u64 819940076#u64 2197884609#u64 3842624034#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5325960299#u64 4946082991#u64 13116530384#u64 8639255073#u64⟩,⟨pack 6254209886#u64 2289188996#u64 8121659814#u64 6426177256#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8739402413#u64 6026869460#u64 18282980612#u64 11257219289#u64⟩,⟨pack 10128294054#u64 5546113887#u64 13410498435#u64 10249066317#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4411647164208536273#u64 847725993289582988#u64 9517640555791048419#u64 2416511473824603637#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 650869303#u32 945513721#u32 1526135784#u32 558694494#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 650869303#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 945513721#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1526135784#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 558694494#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4019707967897605910#u64 2881077900309262512#u64 10554516523350420518#u64 7013669704307935622#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 650869303#u32 945513721#u32 1526135784#u32 558694494#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 650869303#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 945513721#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1526135784#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 650869303#u32) (JFs_TX2_RawMath.extend 945513721#u32) (JFs_TX2_RawMath.extend 1526135784#u32) (JFs_TX2_RawMath.extend 558694494#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 558694494#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails14.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value2_0=
      ok (.Ok (pack 650869303#u32 945513721#u32 1526135784#u32 558694494#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (650869303<2147483647 ∧ 945513721<2147483647) ∧ (1526135784<2147483647 ∧ 558694494<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 650869303#u32 945513721#u32 1526135784#u32 558694494#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5325960299#u64 4946082991#u64 13116530384#u64 8639255073#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 650869303#u32 945513721#u32 1526135784#u32 558694494#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6254209886#u64 2289188996#u64 8121659814#u64 6426177256#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨149467825#u32,1731902166#u32⟩,⟨1103111436#u32,519801054#u32⟩⟩,⟨⟨1538359466#u32,1251146593#u32⟩,⟨525596553#u32,1659131729#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q4_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q4_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=8739402413%2147483647 at h0
  norm_num at h0
  have e0 : a0=149467825#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6026869460%2147483647 at h1
  norm_num at h1
  have e1 : a1=1731902166#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18282980612%2147483647 at h2
  norm_num at h2
  have e2 : a2=1103111436#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11257219289%2147483647 at h3
  norm_num at h3
  have e3 : a3=519801054#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10128294054%2147483647 at h4
  norm_num at h4
  have e4 : a4=1538359466#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5546113887%2147483647 at h5
  norm_num at h5
  have e5 : a5=1251146593#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=13410498435%2147483647 at h6
  norm_num at h6
  have e6 : a6=525596553#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10249066317%2147483647 at h7
  norm_num at h7
  have e7 : a7=1659131729#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q4_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails14.value0_0
      from JFr_TX2_Tails14.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails14.value1_0
      from JFr_TX2_Tails14.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails14.value2_0
      from JFr_TX2_Tails14.source2_0,
    JFz_TX2_Q4_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q4_Raw00.after=JFz_TX2_Q4_Raw01.before := rfl
  have same2 : JFz_TX2_Q4_Raw01.after=JFz_TX2_Q4_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q4_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q4_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q4_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1606296961#u32,2103778778#u32⟩,⟨901120435#u32,1891056613#u32⟩⟩,⟨⟨932407918#u32,1922210071#u32⟩,⟨485445813#u32,2059286268#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1606296961<2147483647 ∧ 2103778778<2147483647) ∧ (901120435<2147483647 ∧ 1891056613<2147483647)) ∧
    ((932407918<2147483647 ∧ 1922210071<2147483647) ∧ (485445813<2147483647 ∧ 2059286268<2147483647))
  omega
theorem addition : decode JFz_TX2_Q4_Head0.value+decode JFz_TX2_Q4_Tail0.value=decode value := by
  change (⟨⟨⟨1456829136,371876612⟩,⟨1945492646,1371255559⟩⟩,⟨⟨1541532099,671063478⟩,⟨2107332907,400154539⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨149467825,1731902166⟩,⟨1103111436,519801054⟩⟩,⟨⟨1538359466,1251146593⟩,⟨525596553,1659131729⟩⟩⟩=⟨⟨⟨1606296961,2103778778⟩,⟨901120435,1891056613⟩⟩,⟨⟨932407918,1922210071⟩,⟨485445813,2059286268⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 4 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q4_Head0.value JFz_TX2_Q4_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q4_Head0.source,
      JFz_TX2_Q4_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q4_Head0.value := by
    change ((1456829136<2147483647 ∧ 371876612<2147483647) ∧ (1945492646<2147483647 ∧ 1371255559<2147483647)) ∧
      ((1541532099<2147483647 ∧ 671063478<2147483647) ∧ (2107332907<2147483647 ∧ 400154539<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q4_Tail0.value := by
    change ((149467825<2147483647 ∧ 1731902166<2147483647) ∧ (1103111436<2147483647 ∧ 519801054<2147483647)) ∧
      ((1538359466<2147483647 ∧ 1251146593<2147483647) ∧ (525596553<2147483647 ∧ 1659131729<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q4_Dot0
end
