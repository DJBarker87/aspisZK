import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails13
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨651351238#u32,1818466289#u32⟩,⟨163529692#u32,1752627827#u32⟩⟩,⟨⟨620898419#u32,1553477790#u32⟩,⟨2002696183#u32,359854502#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 3 3 0 0 26%2147483647=651351238 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*837261247+855639275*299298134+867568255*1113398068+352063*1036534025+1106523000*828424842+1554033304*1976188249+1430280692*911985638+1491718280*1377739529+118514350*2119548747+1675652887*954925640+1364884909*481724260+1135303194*815020164+304762092*129891515+1465393816*1563373211+824208172*1490138206+1752653420*2085015257+1385409049*1171276545+1003904973*1561808778+1298953245*341790181+2005758375*1865522279+497936241*2038128937+235809508*1934570380+1478307182*2010029601+1858903615*313075679+628035096*1289698113+1244951250*947843337)%2147483647=651351238
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 3 3 1 0 26%2147483647=1818466289 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+1483149559*299298134+655227887*1113398068+39062738*1036534025+729079828*828424842+67370206*1976188249+1685049618*911985638+385547620*1377739529+1786803209*2119548747+779721715*954925640+594709522*481724260+338788461*815020164+526756808*129891515+184076238*1563373211+1852498770*1490138206+2102463508*2085015257+1086671526*1171276545+1147694576*1561808778+1504805752*341790181+2005073905*1865522279+185008025*2038128937+1485990146*1934570380+1255280192*2010029601+1018329259*313075679+570157693*1289698113+1511904630*947843337)%2147483647=1818466289
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 3 3 2 0 26%2147483647=163529692 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+1898717401*299298134+1032732628*1113398068+1313565596*1036534025+1074182998*828424842+1410213748*1976188249+1182702806*911985638+321711020*1377739529+2062791928*2119548747+1188803754*954925640+2038502201*481724260+735931834*815020164+1330533011*129891515+1052874750*1563373211+950153811*1490138206+1225424092*2085015257+1659116453*1171276545+1474177753*1561808778+2073609211*341790181+1602919019*1865522279+1865917845*2038128937+1085624123*1934570380+1837870964*2010029601+1550509101*313075679+1661725734*1289698113+2066655336*947843337)%2147483647=163529692
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 3 3 3 0 26%2147483647=1752627827 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+1849775942*299298134+656039795*1113398068+1840648083*1036534025+246996287*828424842+1369248953*1976188249+1132591724*911985638+92744917*1377739529+1719480363*2119548747+1266677922*954925640+377386917*481724260+735227219*815020164+465096431*129891515+451889791*1563373211+1379836302*1490138206+618598847*2085015257+1624084534*1171276545+1511477847*1561808778+1840812326*341790181+185546252*1865522279+2145463598*2038128937+82870699*1934570380+1625323762*2010029601+1843639311*313075679+1777269271*1289698113+1645120956*947843337)%2147483647=1752627827
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 3 3 4 0 26%2147483647=620898419 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+1112406525*299298134+1345999435*1113398068+752376469*1036534025+634588140*828424842+1419170319*1976188249+1702860885*911985638+710076517*1377739529+1256487405*2119548747+1114745059*954925640+1137838899*481724260+1254184109*815020164+1038210451*129891515+274378589*1563373211+171986381*1490138206+1536678585*2085015257+1305878831*1171276545+1335902916*1561808778+1755193245*341790181+2023391453*1865522279+293456010*2038128937+1751078325*1934570380+1423042536*2010029601+1749638204*313075679+1345811362*1289698113+1284924881*947843337)%2147483647=620898419
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 3 3 5 0 26%2147483647=1553477790 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+1796814865*299298134+1253123171*1113398068+1317611639*1036534025+1559245386*828424842+1866942376*1976188249+1973593402*911985638+47019780*1377739529+1353487525*2119548747+1840161555*954925640+2003659556*481724260+200559114*815020164+334988447*129891515+2023650872*1563373211+1296497964*1490138206+34285357*2085015257+1685894190*1171276545+995962325*1561808778+1295624230*341790181+1199631211*1865522279+1948677857*2038128937+1425322328*1934570380+1466877680*2010029601+702011012*313075679+937706871*1289698113+455802666*947843337)%2147483647=1553477790
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 3 3 6 0 26%2147483647=2002696183 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+1838939499*299298134+1353876630*1113398068+1258713036*1036534025+1947503436*828424842+1271796599*1976188249+1660157177*911985638+564707688*1377739529+1858113864*2119548747+1015817431*954925640+1264608004*481724260+735383960*815020164+221696734*129891515+1297524163*1563373211+109088572*1490138206+792206628*2085015257+1921581249*1171276545+94118806*1561808778+476103426*341790181+239612482*1865522279+177052717*2038128937+826458039*1934570380+1923715623*2010029601+1014161165*313075679+1341609618*1289698113+786325583*947843337)%2147483647=2002696183
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 3 3 7 0 26%2147483647=359854502 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*837261247+418714188*299298134+1675147475*1113398068+1674326661*1036534025+547797802*828424842+2073962627*1976188249+897270857*911985638+1582958967*1377739529+49892701*2119548747+1256824732*954925640+1435903714*481724260+742583315*815020164+1789294768*129891515+13407412*1563373211+518661610*1490138206+1259751297*2085015257+1695663205*1171276545+2068940067*1561808778+940478841*341790181+1982757556*1865522279+1956713516*2038128937+863066484*1934570380+522298462*2010029601+1343575777*313075679+771712139*1289698113+157728743*947843337)%2147483647=359854502
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 3 3
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
end AspisR1.JFz_TX2_Q3_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5156932690#u64 3003146977#u64 7817778285#u64 4664668795#u64⟩,⟨pack 2227407715#u64 1660863245#u64 6611855212#u64 5688278094#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 6993689936549602416#u64 4164441306055721030#u64 13215499244857462615#u64 6982398960962651331#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1668417009#u32 813051574#u32 2122521844#u32 1226722723#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1668417009#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 813051574#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2122521844#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1226722723#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4346039203291927585#u64 2439812076311861949#u64 10374682035005708989#u64 8339897811333132944#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1668417009#u32 813051574#u32 2122521844#u32 1226722723#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1668417009#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 813051574#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2122521844#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1668417009#u32) (JFs_TX2_RawMath.extend 813051574#u32) (JFs_TX2_RawMath.extend 2122521844#u32) (JFs_TX2_RawMath.extend 1226722723#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1226722723#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails13.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value0_3=
      ok (.Ok (pack 1668417009#u32 813051574#u32 2122521844#u32 1226722723#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1668417009<2147483647 ∧ 813051574<2147483647) ∧ (2122521844<2147483647 ∧ 1226722723<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1668417009#u32 813051574#u32 2122521844#u32 1226722723#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1668417009#u32 813051574#u32 2122521844#u32 1226722723#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q3_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5156932690#u64 3003146977#u64 7817778285#u64 4664668795#u64⟩,⟨pack 2227407715#u64 1660863245#u64 6611855212#u64 5688278094#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9079113004#u64 5885039290#u64 14042381575#u64 8328340026#u64⟩,⟨pack 6256930465#u64 3749425546#u64 11921488040#u64 8579853227#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4877404254281117235#u64 4075134481179778409#u64 10374834843112326646#u64 5097882579686690139#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 530552265#u32 2035973856#u32 1659042381#u32 386748107#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 530552265#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2035973856#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1659042381#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 386748107#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4465732017215681543#u64 1439925033358435869#u64 9282379253491911612#u64 1886082360454185866#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 530552265#u32 2035973856#u32 1659042381#u32 386748107#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 530552265#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2035973856#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1659042381#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 530552265#u32) (JFs_TX2_RawMath.extend 2035973856#u32) (JFs_TX2_RawMath.extend 1659042381#u32) (JFs_TX2_RawMath.extend 386748107#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 386748107#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails13.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value1_3=
      ok (.Ok (pack 530552265#u32 2035973856#u32 1659042381#u32 386748107#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (530552265<2147483647 ∧ 2035973856<2147483647) ∧ (1659042381<2147483647 ∧ 386748107<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 530552265#u32 2035973856#u32 1659042381#u32 386748107#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5156932690#u64 3003146977#u64 7817778285#u64 4664668795#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 530552265#u32 2035973856#u32 1659042381#u32 386748107#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2227407715#u64 1660863245#u64 6611855212#u64 5688278094#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q3_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9079113004#u64 5885039290#u64 14042381575#u64 8328340026#u64⟩,⟨pack 6256930465#u64 3749425546#u64 11921488040#u64 8579853227#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 12124271990#u64 7893554443#u64 19335252504#u64 11926281944#u64⟩,⟨pack 10486002973#u64 7756727533#u64 18829543877#u64 15632966106#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4656146569417295621#u64 1711206718881965934#u64 9651042409720317233#u64 4344184843943342700#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1710498666#u32 1470835191#u32 1894221342#u32 1518716826#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1710498666#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1470835191#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1894221342#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1518716826#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4929782742242971627#u64 5771685503756159134#u64 10726568639127336557#u64 12453700495724058867#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1710498666#u32 1470835191#u32 1894221342#u32 1518716826#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1710498666#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1470835191#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1894221342#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1710498666#u32) (JFs_TX2_RawMath.extend 1470835191#u32) (JFs_TX2_RawMath.extend 1894221342#u32) (JFs_TX2_RawMath.extend 1518716826#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1518716826#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails13.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value2_3=
      ok (.Ok (pack 1710498666#u32 1470835191#u32 1894221342#u32 1518716826#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1710498666<2147483647 ∧ 1470835191<2147483647) ∧ (1894221342<2147483647 ∧ 1518716826<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1710498666#u32 1470835191#u32 1894221342#u32 1518716826#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 9079113004#u64 5885039290#u64 14042381575#u64 8328340026#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1710498666#u32 1470835191#u32 1894221342#u32 1518716826#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6256930465#u64 3749425546#u64 11921488040#u64 8579853227#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q3_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1386853755#u32,1451103502#u32⟩,⟨7899681#u32,1188863709#u32⟩⟩,⟨⟨1896068385#u32,1314276592#u32⟩,⟨1649674701#u32,600580577#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q3_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q3_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12124271990%2147483647 at h0
  norm_num at h0
  have e0 : a0=1386853755#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7893554443%2147483647 at h1
  norm_num at h1
  have e1 : a1=1451103502#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19335252504%2147483647 at h2
  norm_num at h2
  have e2 : a2=7899681#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11926281944%2147483647 at h3
  norm_num at h3
  have e3 : a3=1188863709#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10486002973%2147483647 at h4
  norm_num at h4
  have e4 : a4=1896068385#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7756727533%2147483647 at h5
  norm_num at h5
  have e5 : a5=1314276592#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=18829543877%2147483647 at h6
  norm_num at h6
  have e6 : a6=1649674701#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=15632966106%2147483647 at h7
  norm_num at h7
  have e7 : a7=600580577#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q3_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails13.value0_3
      from JFr_TX2_Tails13.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails13.value1_3
      from JFr_TX2_Tails13.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails13.value2_3
      from JFr_TX2_Tails13.source2_3,
    JFz_TX2_Q3_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q3_Raw30.after=JFz_TX2_Q3_Raw31.before := rfl
  have same2 : JFz_TX2_Q3_Raw31.after=JFz_TX2_Q3_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q3_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q3_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q3_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨2038204993#u32,1122086144#u32⟩,⟨171429373#u32,794007889#u32⟩⟩,⟨⟨369483157#u32,720270735#u32⟩,⟨1504887237#u32,960435079#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2038204993<2147483647 ∧ 1122086144<2147483647) ∧ (171429373<2147483647 ∧ 794007889<2147483647)) ∧
    ((369483157<2147483647 ∧ 720270735<2147483647) ∧ (1504887237<2147483647 ∧ 960435079<2147483647))
  omega
theorem addition : decode JFz_TX2_Q3_Head3.value+decode JFz_TX2_Q3_Tail3.value=decode value := by
  change (⟨⟨⟨651351238,1818466289⟩,⟨163529692,1752627827⟩⟩,⟨⟨620898419,1553477790⟩,⟨2002696183,359854502⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1386853755,1451103502⟩,⟨7899681,1188863709⟩⟩,⟨⟨1896068385,1314276592⟩,⟨1649674701,600580577⟩⟩⟩=⟨⟨⟨2038204993,1122086144⟩,⟨171429373,794007889⟩⟩,⟨⟨369483157,720270735⟩,⟨1504887237,960435079⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 3 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q3_Head3.value JFz_TX2_Q3_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q3_Head3.source,
      JFz_TX2_Q3_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q3_Head3.value := by
    change ((651351238<2147483647 ∧ 1818466289<2147483647) ∧ (163529692<2147483647 ∧ 1752627827<2147483647)) ∧
      ((620898419<2147483647 ∧ 1553477790<2147483647) ∧ (2002696183<2147483647 ∧ 359854502<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q3_Tail3.value := by
    change ((1386853755<2147483647 ∧ 1451103502<2147483647) ∧ (7899681<2147483647 ∧ 1188863709<2147483647)) ∧
      ((1896068385<2147483647 ∧ 1314276592<2147483647) ∧ (1649674701<2147483647 ∧ 600580577<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q3_Dot3
end
