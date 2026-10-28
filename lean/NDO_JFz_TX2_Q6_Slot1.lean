import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails16
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨794261776#u32,447243281#u32⟩,⟨585076230#u32,560873498#u32⟩⟩,⟨⟨483009444#u32,68756273#u32⟩,⟨272238577#u32,226475935#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 6 1 0 0 26%2147483647=794261776 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*695360746+855639275*842825581+867568255*1574748103+352063*1476772418+1106523000*1060963918+1554033304*1257392821+1430280692*349216029+1491718280*1725521798+118514350*401170618+1675652887*2136940553+1364884909*1006126177+1135303194*1983824884+304762092*348560654+1465393816*1138153347+824208172*824099658+1752653420*1044538076+1385409049*1182881409+1003904973*1033615254+1298953245*1786857940+2005758375*429655735+497936241*1518083864+235809508*512432018+1478307182*387358185+1858903615*2097632150+628035096*849078159+1244951250*782367421)%2147483647=794261776
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 6 1 1 0 26%2147483647=447243281 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+1483149559*842825581+655227887*1574748103+39062738*1476772418+729079828*1060963918+67370206*1257392821+1685049618*349216029+385547620*1725521798+1786803209*401170618+779721715*2136940553+594709522*1006126177+338788461*1983824884+526756808*348560654+184076238*1138153347+1852498770*824099658+2102463508*1044538076+1086671526*1182881409+1147694576*1033615254+1504805752*1786857940+2005073905*429655735+185008025*1518083864+1485990146*512432018+1255280192*387358185+1018329259*2097632150+570157693*849078159+1511904630*782367421)%2147483647=447243281
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 6 1 2 0 26%2147483647=585076230 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+1898717401*842825581+1032732628*1574748103+1313565596*1476772418+1074182998*1060963918+1410213748*1257392821+1182702806*349216029+321711020*1725521798+2062791928*401170618+1188803754*2136940553+2038502201*1006126177+735931834*1983824884+1330533011*348560654+1052874750*1138153347+950153811*824099658+1225424092*1044538076+1659116453*1182881409+1474177753*1033615254+2073609211*1786857940+1602919019*429655735+1865917845*1518083864+1085624123*512432018+1837870964*387358185+1550509101*2097632150+1661725734*849078159+2066655336*782367421)%2147483647=585076230
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 6 1 3 0 26%2147483647=560873498 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+1849775942*842825581+656039795*1574748103+1840648083*1476772418+246996287*1060963918+1369248953*1257392821+1132591724*349216029+92744917*1725521798+1719480363*401170618+1266677922*2136940553+377386917*1006126177+735227219*1983824884+465096431*348560654+451889791*1138153347+1379836302*824099658+618598847*1044538076+1624084534*1182881409+1511477847*1033615254+1840812326*1786857940+185546252*429655735+2145463598*1518083864+82870699*512432018+1625323762*387358185+1843639311*2097632150+1777269271*849078159+1645120956*782367421)%2147483647=560873498
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 6 1 4 0 26%2147483647=483009444 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+1112406525*842825581+1345999435*1574748103+752376469*1476772418+634588140*1060963918+1419170319*1257392821+1702860885*349216029+710076517*1725521798+1256487405*401170618+1114745059*2136940553+1137838899*1006126177+1254184109*1983824884+1038210451*348560654+274378589*1138153347+171986381*824099658+1536678585*1044538076+1305878831*1182881409+1335902916*1033615254+1755193245*1786857940+2023391453*429655735+293456010*1518083864+1751078325*512432018+1423042536*387358185+1749638204*2097632150+1345811362*849078159+1284924881*782367421)%2147483647=483009444
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 6 1 5 0 26%2147483647=68756273 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+1796814865*842825581+1253123171*1574748103+1317611639*1476772418+1559245386*1060963918+1866942376*1257392821+1973593402*349216029+47019780*1725521798+1353487525*401170618+1840161555*2136940553+2003659556*1006126177+200559114*1983824884+334988447*348560654+2023650872*1138153347+1296497964*824099658+34285357*1044538076+1685894190*1182881409+995962325*1033615254+1295624230*1786857940+1199631211*429655735+1948677857*1518083864+1425322328*512432018+1466877680*387358185+702011012*2097632150+937706871*849078159+455802666*782367421)%2147483647=68756273
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 6 1 6 0 26%2147483647=272238577 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+1838939499*842825581+1353876630*1574748103+1258713036*1476772418+1947503436*1060963918+1271796599*1257392821+1660157177*349216029+564707688*1725521798+1858113864*401170618+1015817431*2136940553+1264608004*1006126177+735383960*1983824884+221696734*348560654+1297524163*1138153347+109088572*824099658+792206628*1044538076+1921581249*1182881409+94118806*1033615254+476103426*1786857940+239612482*429655735+177052717*1518083864+826458039*512432018+1923715623*387358185+1014161165*2097632150+1341609618*849078159+786325583*782367421)%2147483647=272238577
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 6 1 7 0 26%2147483647=226475935 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*695360746+418714188*842825581+1675147475*1574748103+1674326661*1476772418+547797802*1060963918+2073962627*1257392821+897270857*349216029+1582958967*1725521798+49892701*401170618+1256824732*2136940553+1435903714*1006126177+742583315*1983824884+1789294768*348560654+13407412*1138153347+518661610*824099658+1259751297*1044538076+1695663205*1182881409+2068940067*1033615254+940478841*1786857940+1982757556*429655735+1956713516*1518083864+863066484*512432018+522298462*387358185+1343575777*2097632150+771712139*849078159+157728743*782367421)%2147483647=226475935
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 6 1
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
end AspisR1.JFz_TX2_Q6_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3929522417#u64 2299140497#u64 5181574644#u64 1936594270#u64⟩,⟨pack 3463582290#u64 1974639964#u64 5186770758#u64 1874380428#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4398042265262868651#u64 2286781140281953000#u64 10252697040358654638#u64 3172703143857138680#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 429577892#u32 777769183#u32 793526996#u32 551180089#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 429577892#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 777769183#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 793526996#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 551180089#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3835926426498510029#u64 882399295212669541#u64 8151483926425636964#u64 3726860317503248159#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 429577892#u32 777769183#u32 793526996#u32 551180089#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 429577892#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 777769183#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 793526996#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 429577892#u32) (JFs_TX2_RawMath.extend 777769183#u32) (JFs_TX2_RawMath.extend 793526996#u32) (JFs_TX2_RawMath.extend 551180089#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 551180089#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails16.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value0_1=
      ok (.Ok (pack 429577892#u32 777769183#u32 793526996#u32 551180089#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (429577892<2147483647 ∧ 777769183<2147483647) ∧ (793526996<2147483647 ∧ 551180089<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 429577892#u32 777769183#u32 793526996#u32 551180089#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 429577892#u32 777769183#u32 793526996#u32 551180089#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q6_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3929522417#u64 2299140497#u64 5181574644#u64 1936594270#u64⟩,⟨pack 3463582290#u64 1974639964#u64 5186770758#u64 1874380428#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9209667240#u64 3135930285#u64 13325173638#u64 3919270044#u64⟩,⟨pack 6360223549#u64 3782922789#u64 10249775621#u64 4168708704#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6933043046418899426#u64 500738714246999986#u64 14274132720215237993#u64 3671726037206830205#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1223156773#u32 27705771#u32 1841319527#u32 710338939#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1223156773#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 27705771#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1841319527#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 710338939#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5393706701926081941#u64 311065743970399103#u64 10786986491962797215#u64 1610209094370554509#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1223156773#u32 27705771#u32 1841319527#u32 710338939#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1223156773#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 27705771#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1841319527#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1223156773#u32) (JFs_TX2_RawMath.extend 27705771#u32) (JFs_TX2_RawMath.extend 1841319527#u32) (JFs_TX2_RawMath.extend 710338939#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 710338939#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails16.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value1_1=
      ok (.Ok (pack 1223156773#u32 27705771#u32 1841319527#u32 710338939#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1223156773<2147483647 ∧ 27705771<2147483647) ∧ (1841319527<2147483647 ∧ 710338939<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1223156773#u32 27705771#u32 1841319527#u32 710338939#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3929522417#u64 2299140497#u64 5181574644#u64 1936594270#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1223156773#u32 27705771#u32 1841319527#u32 710338939#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3463582290#u64 1974639964#u64 5186770758#u64 1874380428#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9209667240#u64 3135930285#u64 13325173638#u64 3919270044#u64⟩,⟨pack 6360223549#u64 3782922789#u64 10249775621#u64 4168708704#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 13216435695#u64 4326337203#u64 17149839017#u64 7114927999#u64⟩,⟨pack 8466858753#u64 7592900187#u64 14190384704#u64 9454706403#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4028964421412776881#u64 1324205690003332840#u64 7990926711047639072#u64 2893117082267617683#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 777559008#u32 1740878835#u32 337840531#u32 1322547246#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 777559008#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1740878835#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 337840531#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1322547246#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2774776365563296502#u64 4526975336473267212#u64 5848167809507340533#u64 8097053299201861213#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 777559008#u32 1740878835#u32 337840531#u32 1322547246#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 777559008#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1740878835#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 337840531#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 777559008#u32) (JFs_TX2_RawMath.extend 1740878835#u32) (JFs_TX2_RawMath.extend 337840531#u32) (JFs_TX2_RawMath.extend 1322547246#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1322547246#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails16.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value2_1=
      ok (.Ok (pack 777559008#u32 1740878835#u32 337840531#u32 1322547246#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (777559008<2147483647 ∧ 1740878835<2147483647) ∧ (337840531<2147483647 ∧ 1322547246<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 777559008#u32 1740878835#u32 337840531#u32 1322547246#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 9209667240#u64 3135930285#u64 13325173638#u64 3919270044#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 777559008#u32 1740878835#u32 337840531#u32 1322547246#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6360223549#u64 3782922789#u64 10249775621#u64 4168708704#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨331533813#u32,31369909#u32⟩,⟨2117453488#u32,672477058#u32⟩⟩,⟨⟨2024407812#u32,1150449246#u32⟩,⟨1305482822#u32,864771815#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q6_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q6_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=13216435695%2147483647 at h0
  norm_num at h0
  have e0 : a0=331533813#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=4326337203%2147483647 at h1
  norm_num at h1
  have e1 : a1=31369909#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17149839017%2147483647 at h2
  norm_num at h2
  have e2 : a2=2117453488#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7114927999%2147483647 at h3
  norm_num at h3
  have e3 : a3=672477058#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8466858753%2147483647 at h4
  norm_num at h4
  have e4 : a4=2024407812#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7592900187%2147483647 at h5
  norm_num at h5
  have e5 : a5=1150449246#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14190384704%2147483647 at h6
  norm_num at h6
  have e6 : a6=1305482822#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9454706403%2147483647 at h7
  norm_num at h7
  have e7 : a7=864771815#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q6_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails16.value0_1
      from JFr_TX2_Tails16.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails16.value1_1
      from JFr_TX2_Tails16.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails16.value2_1
      from JFr_TX2_Tails16.source2_1,
    JFz_TX2_Q6_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q6_Raw10.after=JFz_TX2_Q6_Raw11.before := rfl
  have same2 : JFz_TX2_Q6_Raw11.after=JFz_TX2_Q6_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q6_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q6_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q6_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1125795589#u32,478613190#u32⟩,⟨555046071#u32,1233350556#u32⟩⟩,⟨⟨359933609#u32,1219205519#u32⟩,⟨1577721399#u32,1091247750#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1125795589<2147483647 ∧ 478613190<2147483647) ∧ (555046071<2147483647 ∧ 1233350556<2147483647)) ∧
    ((359933609<2147483647 ∧ 1219205519<2147483647) ∧ (1577721399<2147483647 ∧ 1091247750<2147483647))
  omega
theorem addition : decode JFz_TX2_Q6_Head1.value+decode JFz_TX2_Q6_Tail1.value=decode value := by
  change (⟨⟨⟨794261776,447243281⟩,⟨585076230,560873498⟩⟩,⟨⟨483009444,68756273⟩,⟨272238577,226475935⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨331533813,31369909⟩,⟨2117453488,672477058⟩⟩,⟨⟨2024407812,1150449246⟩,⟨1305482822,864771815⟩⟩⟩=⟨⟨⟨1125795589,478613190⟩,⟨555046071,1233350556⟩⟩,⟨⟨359933609,1219205519⟩,⟨1577721399,1091247750⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 6 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q6_Head1.value JFz_TX2_Q6_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q6_Head1.source,
      JFz_TX2_Q6_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q6_Head1.value := by
    change ((794261776<2147483647 ∧ 447243281<2147483647) ∧ (585076230<2147483647 ∧ 560873498<2147483647)) ∧
      ((483009444<2147483647 ∧ 68756273<2147483647) ∧ (272238577<2147483647 ∧ 226475935<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q6_Tail1.value := by
    change ((331533813<2147483647 ∧ 31369909<2147483647) ∧ (2117453488<2147483647 ∧ 672477058<2147483647)) ∧
      ((2024407812<2147483647 ∧ 1150449246<2147483647) ∧ (1305482822<2147483647 ∧ 864771815<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q6_Dot1
end
