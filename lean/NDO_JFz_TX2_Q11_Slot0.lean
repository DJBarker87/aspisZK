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
namespace AspisR1.JFz_TX2_Q11_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨102918456#u32,1729212114#u32⟩,⟨636340811#u32,1722216785#u32⟩⟩,⟨⟨1608807152#u32,1432584934#u32⟩,⟨548930347#u32,1483748742#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 11 0 0 0 26%2147483647=102918456 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1998579918+855639275*123189145+867568255*1180253962+352063*1655965776+1106523000*1999448922+1554033304*1012263825+1430280692*2065149666+1491718280*32985080+118514350*319155351+1675652887*194207598+1364884909*1120523427+1135303194*315465451+304762092*684414194+1465393816*1937444752+824208172*1211941725+1752653420*2071630736+1385409049*672281323+1003904973*355162570+1298953245*268909693+2005758375*2122043116+497936241*562106540+235809508*1536183630+1478307182*1329889675+1858903615*901461949+628035096*555970472+1244951250*480693659)%2147483647=102918456
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 11 0 1 0 26%2147483647=1729212114 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+1483149559*123189145+655227887*1180253962+39062738*1655965776+729079828*1999448922+67370206*1012263825+1685049618*2065149666+385547620*32985080+1786803209*319155351+779721715*194207598+594709522*1120523427+338788461*315465451+526756808*684414194+184076238*1937444752+1852498770*1211941725+2102463508*2071630736+1086671526*672281323+1147694576*355162570+1504805752*268909693+2005073905*2122043116+185008025*562106540+1485990146*1536183630+1255280192*1329889675+1018329259*901461949+570157693*555970472+1511904630*480693659)%2147483647=1729212114
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 11 0 2 0 26%2147483647=636340811 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+1898717401*123189145+1032732628*1180253962+1313565596*1655965776+1074182998*1999448922+1410213748*1012263825+1182702806*2065149666+321711020*32985080+2062791928*319155351+1188803754*194207598+2038502201*1120523427+735931834*315465451+1330533011*684414194+1052874750*1937444752+950153811*1211941725+1225424092*2071630736+1659116453*672281323+1474177753*355162570+2073609211*268909693+1602919019*2122043116+1865917845*562106540+1085624123*1536183630+1837870964*1329889675+1550509101*901461949+1661725734*555970472+2066655336*480693659)%2147483647=636340811
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 11 0 3 0 26%2147483647=1722216785 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+1849775942*123189145+656039795*1180253962+1840648083*1655965776+246996287*1999448922+1369248953*1012263825+1132591724*2065149666+92744917*32985080+1719480363*319155351+1266677922*194207598+377386917*1120523427+735227219*315465451+465096431*684414194+451889791*1937444752+1379836302*1211941725+618598847*2071630736+1624084534*672281323+1511477847*355162570+1840812326*268909693+185546252*2122043116+2145463598*562106540+82870699*1536183630+1625323762*1329889675+1843639311*901461949+1777269271*555970472+1645120956*480693659)%2147483647=1722216785
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 11 0 4 0 26%2147483647=1608807152 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+1112406525*123189145+1345999435*1180253962+752376469*1655965776+634588140*1999448922+1419170319*1012263825+1702860885*2065149666+710076517*32985080+1256487405*319155351+1114745059*194207598+1137838899*1120523427+1254184109*315465451+1038210451*684414194+274378589*1937444752+171986381*1211941725+1536678585*2071630736+1305878831*672281323+1335902916*355162570+1755193245*268909693+2023391453*2122043116+293456010*562106540+1751078325*1536183630+1423042536*1329889675+1749638204*901461949+1345811362*555970472+1284924881*480693659)%2147483647=1608807152
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 11 0 5 0 26%2147483647=1432584934 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+1796814865*123189145+1253123171*1180253962+1317611639*1655965776+1559245386*1999448922+1866942376*1012263825+1973593402*2065149666+47019780*32985080+1353487525*319155351+1840161555*194207598+2003659556*1120523427+200559114*315465451+334988447*684414194+2023650872*1937444752+1296497964*1211941725+34285357*2071630736+1685894190*672281323+995962325*355162570+1295624230*268909693+1199631211*2122043116+1948677857*562106540+1425322328*1536183630+1466877680*1329889675+702011012*901461949+937706871*555970472+455802666*480693659)%2147483647=1432584934
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 11 0 6 0 26%2147483647=548930347 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+1838939499*123189145+1353876630*1180253962+1258713036*1655965776+1947503436*1999448922+1271796599*1012263825+1660157177*2065149666+564707688*32985080+1858113864*319155351+1015817431*194207598+1264608004*1120523427+735383960*315465451+221696734*684414194+1297524163*1937444752+109088572*1211941725+792206628*2071630736+1921581249*672281323+94118806*355162570+476103426*268909693+239612482*2122043116+177052717*562106540+826458039*1536183630+1923715623*1329889675+1014161165*901461949+1341609618*555970472+786325583*480693659)%2147483647=548930347
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 11 0 7 0 26%2147483647=1483748742 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1998579918+418714188*123189145+1675147475*1180253962+1674326661*1655965776+547797802*1999448922+2073962627*1012263825+897270857*2065149666+1582958967*32985080+49892701*319155351+1256824732*194207598+1435903714*1120523427+742583315*315465451+1789294768*684414194+13407412*1937444752+518661610*1211941725+1259751297*2071630736+1695663205*672281323+2068940067*355162570+940478841*268909693+1982757556*2122043116+1956713516*562106540+863066484*1536183630+522298462*1329889675+1343575777*901461949+771712139*555970472+157728743*480693659)%2147483647=1483748742
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 11 0
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
end AspisR1.JFz_TX2_Q11_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5989198514#u64 3237784548#u64 6413025545#u64 1700917811#u64⟩,⟨pack 4219446128#u64 1733980300#u64 5904658569#u64 3361964518#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 8286683886268415109#u64 3283739577400446054#u64 12194173776334303271#u64 2407907738589641610#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1890129620#u32 249905512#u32 772658478#u32 208999261#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1890129620#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 249905512#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 772658478#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 208999261#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5145980198833569789#u64 2463871873280611256#u64 12667555368639499149#u64 5511497840434214331#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1890129620#u32 249905512#u32 772658478#u32 208999261#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1890129620#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 249905512#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 772658478#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1890129620#u32) (JFs_TX2_RawMath.extend 249905512#u32) (JFs_TX2_RawMath.extend 772658478#u32) (JFs_TX2_RawMath.extend 208999261#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 208999261#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails21.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value0_0=
      ok (.Ok (pack 1890129620#u32 249905512#u32 772658478#u32 208999261#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1890129620<2147483647 ∧ 249905512<2147483647) ∧ (772658478<2147483647 ∧ 208999261<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1890129620#u32 249905512#u32 772658478#u32 208999261#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1890129620#u32 249905512#u32 772658478#u32 208999261#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q11_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5989198514#u64 3237784548#u64 6413025545#u64 1700917811#u64⟩,⟨pack 4219446128#u64 1733980300#u64 5904658569#u64 3361964518#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10522763347#u64 5758909123#u64 13045767224#u64 5257000092#u64⟩,⟨pack 6864293821#u64 3337667822#u64 12131211640#u64 5563749459#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7367719926535678248#u64 2761709048244875105#u64 10822742353953121671#u64 4909219552710322193#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1662852037#u32 1129385425#u32 394323931#u32 467277555#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1662852037#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1129385425#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 394323931#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 467277555#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5413129044141446126#u64 1126801148826610953#u64 9485705295324359557#u64 1864175550516350683#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1662852037#u32 1129385425#u32 394323931#u32 467277555#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1662852037#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1129385425#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 394323931#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1662852037#u32) (JFs_TX2_RawMath.extend 1129385425#u32) (JFs_TX2_RawMath.extend 394323931#u32) (JFs_TX2_RawMath.extend 467277555#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 467277555#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails21.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value1_0=
      ok (.Ok (pack 1662852037#u32 1129385425#u32 394323931#u32 467277555#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1662852037<2147483647 ∧ 1129385425<2147483647) ∧ (394323931<2147483647 ∧ 467277555<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1662852037#u32 1129385425#u32 394323931#u32 467277555#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5989198514#u64 3237784548#u64 6413025545#u64 1700917811#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1662852037#u32 1129385425#u32 394323931#u32 467277555#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4219446128#u64 1733980300#u64 5904658569#u64 3361964518#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10522763347#u64 5758909123#u64 13045767224#u64 5257000092#u64⟩,⟨pack 6864293821#u64 3337667822#u64 12131211640#u64 5563749459#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 13724830797#u64 8211650491#u64 18789225591#u64 6947187834#u64⟩,⟨pack 8277976649#u64 6908034307#u64 17241167126#u64 11728449682#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 3830154505589934469#u64 1180824495987595706#u64 8044836442361051138#u64 3622095759244373520#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 461605845#u32 1808156817#u32 1551356965#u32 1769828870#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 461605845#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1808156817#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1551356965#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1769828870#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2089629674459324496#u64 4062523925317124125#u64 6380514502663435098#u64 10698624058603311220#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 461605845#u32 1808156817#u32 1551356965#u32 1769828870#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 461605845#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1808156817#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1551356965#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 461605845#u32) (JFs_TX2_RawMath.extend 1808156817#u32) (JFs_TX2_RawMath.extend 1551356965#u32) (JFs_TX2_RawMath.extend 1769828870#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1769828870#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails21.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails21.value2_0=
      ok (.Ok (pack 461605845#u32 1808156817#u32 1551356965#u32 1769828870#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (461605845<2147483647 ∧ 1808156817<2147483647) ∧ (1551356965<2147483647 ∧ 1769828870<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 461605845#u32 1808156817#u32 1551356965#u32 1769828870#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 10522763347#u64 5758909123#u64 13045767224#u64 5257000092#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 461605845#u32 1808156817#u32 1551356965#u32 1769828870#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6864293821#u64 3337667822#u64 12131211640#u64 5563749459#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q11_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨839928915#u32,1769199550#u32⟩,⟨1609356415#u32,504736893#u32⟩⟩,⟨⟨1835525708#u32,465583366#u32⟩,⟨61297950#u32,991031447#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q11_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q11_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=13724830797%2147483647 at h0
  norm_num at h0
  have e0 : a0=839928915#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8211650491%2147483647 at h1
  norm_num at h1
  have e1 : a1=1769199550#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18789225591%2147483647 at h2
  norm_num at h2
  have e2 : a2=1609356415#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=6947187834%2147483647 at h3
  norm_num at h3
  have e3 : a3=504736893#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8277976649%2147483647 at h4
  norm_num at h4
  have e4 : a4=1835525708#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6908034307%2147483647 at h5
  norm_num at h5
  have e5 : a5=465583366#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17241167126%2147483647 at h6
  norm_num at h6
  have e6 : a6=61297950#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11728449682%2147483647 at h7
  norm_num at h7
  have e7 : a7=991031447#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q11_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails21.value0_0
      from JFr_TX2_Tails21.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails21.value1_0
      from JFr_TX2_Tails21.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 11))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails21.value2_0
      from JFr_TX2_Tails21.source2_0,
    JFz_TX2_Q11_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q11_Raw00.after=JFz_TX2_Q11_Raw01.before := rfl
  have same2 : JFz_TX2_Q11_Raw01.after=JFz_TX2_Q11_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q11_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q11_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q11_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨942847371#u32,1350928017#u32⟩,⟨98213579#u32,79470031#u32⟩⟩,⟨⟨1296849213#u32,1898168300#u32⟩,⟨610228297#u32,327296542#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((942847371<2147483647 ∧ 1350928017<2147483647) ∧ (98213579<2147483647 ∧ 79470031<2147483647)) ∧
    ((1296849213<2147483647 ∧ 1898168300<2147483647) ∧ (610228297<2147483647 ∧ 327296542<2147483647))
  omega
theorem addition : decode JFz_TX2_Q11_Head0.value+decode JFz_TX2_Q11_Tail0.value=decode value := by
  change (⟨⟨⟨102918456,1729212114⟩,⟨636340811,1722216785⟩⟩,⟨⟨1608807152,1432584934⟩,⟨548930347,1483748742⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨839928915,1769199550⟩,⟨1609356415,504736893⟩⟩,⟨⟨1835525708,465583366⟩,⟨61297950,991031447⟩⟩⟩=⟨⟨⟨942847371,1350928017⟩,⟨98213579,79470031⟩⟩,⟨⟨1296849213,1898168300⟩,⟨610228297,327296542⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 11)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 11 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q11_Head0.value JFz_TX2_Q11_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q11_Head0.source,
      JFz_TX2_Q11_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q11_Head0.value := by
    change ((102918456<2147483647 ∧ 1729212114<2147483647) ∧ (636340811<2147483647 ∧ 1722216785<2147483647)) ∧
      ((1608807152<2147483647 ∧ 1432584934<2147483647) ∧ (548930347<2147483647 ∧ 1483748742<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q11_Tail0.value := by
    change ((839928915<2147483647 ∧ 1769199550<2147483647) ∧ (1609356415<2147483647 ∧ 504736893<2147483647)) ∧
      ((1835525708<2147483647 ∧ 465583366<2147483647) ∧ (61297950<2147483647 ∧ 991031447<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q11_Dot0
end
