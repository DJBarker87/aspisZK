import R1Z.PV_RunJoin_IndexedPair19
import R1Z.PV_RunJoin_PathCell1016
import R1Z.PV_RunJoin_PathCell1116
import R1Z.PV_RunJoin_PathCell1216
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell1019
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,1075778621#u32,569932161#u32,1744169643#u32,1373371366#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_PathModel16.s_10_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [424376309#u32,203451508#u32,381510423#u32,1461787452#u32,491108136#u32,2070846719#u32,683574778#u32,300498066#u32,2102162553#u32,1839272683#u32,19359865#u32,602266835#u32,1050642011#u32,787752141#u32,1159764581#u32,646708922#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_PathModel16.s_10_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [178963357#u32,2114140411#u32,1107451126#u32,817202022#u32,1601167497#u32,733072880#u32,748875890#u32,1813547856#u32,1636810313#u32,1347883191#u32,1945252541#u32,1869532975#u32,1712439597#u32,704903902#u32,1207865688#u32,1713068769#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_PathModel16.s_10_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [1643903669#u32,560200127#u32,756563490#u32,1308256023#u32,1503415045#u32,460549615#u32,1699312912#u32,1191600235#u32,214428930#u32,224814534#u32,1685193324#u32,1705062574#u32,1093676010#u32,146171243#u32,1627360716#u32,1020313726#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_PathModel16.s_10_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [202281931#u32,75950143#u32,1293029030#u32,1560350476#u32,878129945#u32,1113670399#u32,1872772449#u32,1489142334#u32,1490148784#u32,2078365092#u32,1923595769#u32,663009355#u32,847494096#u32,897213410#u32,1538854314#u32,1220507837#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_PathModel16.s_10_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [1262910163#u32,400941949#u32,195986847#u32,2115242737#u32,582367138#u32,615098069#u32,1786367886#u32,1884180021#u32,1410744327#u32,1141015543#u32,1349849979#u32,1835037269#u32,831798152#u32,1049633697#u32,1791316598#u32,2044617035#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_PathModel16.s_10_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [1454128805#u32,507985639#u32,499017384#u32,2125563697#u32,471013500#u32,1358678206#u32,1436241220#u32,435480802#u32,293691198#u32,149246706#u32,1521437165#u32,226933014#u32,231892943#u32,256490162#u32,798803503#u32,1739411238#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_PathModel16.s_10_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [2079576675#u32,1057345248#u32,1547394377#u32,461679809#u32,22500315#u32,813374435#u32,1411922062#u32,502843526#u32,1634610954#u32,101810699#u32,1575372494#u32,206565802#u32,1840804717#u32,258676638#u32,64372630#u32,1877303123#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_PathModel16.s_10_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1784158610#u32,256536532#u32,146496391#u32,1045910520#u32,1526677451#u32,1475764009#u32,1431024328#u32,1316405890#u32,123479637#u32,1640410111#u32,1767889890#u32,1331643005#u32,1588747361#u32,371992745#u32,1880073417#u32,798523582#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_PathModel16.s_10_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1899496193#u32,1695419019#u32,1731875269#u32,1327557273#u32,767400213#u32,1428786514#u32,2134504396#u32,1936997214#u32,64406847#u32,477076091#u32,1429415426#u32,1240167587#u32,558879332#u32,1609426381#u32,673745607#u32,1451358696#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_PathModel16.s_10_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1961392519#u32,280836231#u32,2049167750#u32,1748162657#u32,429651622#u32,2118648613#u32,317564827#u32,146671029#u32,387042687#u32,457812276#u32,2017933476#u32,1660512056#u32,637253199#u32,623025650#u32,1897059875#u32,630708991#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_PathModel16.s_10_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [466471828#u32,553695223#u32,76227198#u32,823058679#u32,1562588321#u32,1958982095#u32,1844998868#u32,1069870260#u32,422199047#u32,1508684710#u32,757470002#u32,649530319#u32,118319343#u32,935334401#u32,2069196930#u32,1799539359#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_PathModel16.s_10_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [349862439#u32,290967589#u32,2037210409#u32,882023435#u32,1500560699#u32,1016214828#u32,795177673#u32,1636975949#u32,91659207#u32,1560985313#u32,144957847#u32,1628704004#u32,494205425#u32,1960277005#u32,681087875#u32,989261491#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_PathModel16.s_10_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [842575859#u32,804158170#u32,292644105#u32,1893800674#u32,1780257938#u32,1740242300#u32,189072353#u32,52952614#u32,1508150842#u32,693472367#u32,773654266#u32,1600583383#u32,1037357586#u32,2073699616#u32,1750618957#u32,222961827#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_PathModel16.s_10_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1172839063#u32,246318398#u32,27448438#u32,574911983#u32,799321850#u32,1516233264#u32,1197508230#u32,683643877#u32,1359423421#u32,877427126#u32,1390146516#u32,1311606352#u32,2030197208#u32,1745373232#u32,140964540#u32,2137203959#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_PathModel16.s_10_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [553901348#u32,1703102780#u32,1511681258#u32,1608948667#u32,1408908241#u32,2094196489#u32,1122342096#u32,112835923#u32,1516806863#u32,592345703#u32,1185158805#u32,792317380#u32,571466303#u32,1759574018#u32,1345506405#u32,2077016772#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_PathModel16.s_10_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [899493848#u32,953318692#u32,126094781#u32,1391043286#u32,1931547252#u32,545105031#u32,805424632#u32,29264043#u32,127966146#u32,566860590#u32,1672055324#u32,1881897422#u32,1335303275#u32,290449496#u32,964822042#u32,370420609#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_PathModel16.s_10_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [635123875#u32,531536295#u32,1977890812#u32,847423453#u32,2145693737#u32,1857447158#u32,1729485710#u32,1451116355#u32,925498762#u32,813124294#u32,218402720#u32,511249032#u32,1248432232#u32,1626481962#u32,1760122372#u32,308103339#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_PathModel16.s_10_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1798299775#u32,277514634#u32,1554276316#u32,988188504#u32,1879142706#u32,1547845456#u32,1402429884#u32,275628238#u32,98219290#u32,1747367491#u32,52064331#u32,25457586#u32,585695869#u32,2049351771#u32,467556556#u32,965153949#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_PathModel16.s_10_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [831877060#u32,1507618972#u32,43689676#u32,887891060#u32,1230860457#u32,225827870#u32,1010704039#u32,1690442394#u32,917271576#u32,1879583458#u32,856888107#u32,277677891#u32,1772195788#u32,1902699557#u32,1974993648#u32,1575967264#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_PathModel16.s_10_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1343415099#u32,1305202528#u32,56671679#u32,1354579560#u32,2052902330#u32,1152529751#u32,1861685947#u32,1906836630#u32,647401813#u32,823439291#u32,374705722#u32,407814028#u32,895517377#u32,478700294#u32,1539423895#u32,1634583166#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_PathModel16.s_10_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [719737753#u32,1083942124#u32,1648371752#u32,1553796582#u32,1985361847#u32,1887855098#u32,536690820#u32,581041814#u32,261618817#u32,1483661371#u32,723236334#u32,1091134021#u32,371561686#u32,1616577669#u32,58733187#u32,1739651156#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_PathModel16.s_10_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1405131205#u32,153856201#u32,1873932058#u32,1544707081#u32,326127039#u32,109834822#u32,1772138921#u32,1144644588#u32,1403922055#u32,1565860819#u32,314634411#u32,1796088065#u32,1941092767#u32,753088909#u32,459763337#u32,255643292#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_PathModel16.s_10_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,896398700#u32,194579163#u32,2020233505#u32,1152165187#u32,627717744#u32,1600797184#u32,944953572#u32,1273900178#u32,1214065769#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_PathModel16.s_10_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift23
theorem canon23 : Canonical s23 := by
  intro i
  fin_cases i <;> decide
#print axioms canon23
theorem external : poseidon2.external_linear_lazy s0 = ok s1 := by
  obtain ⟨out,ho,hc,hm⟩ := PV_Src_ExternalModel.source (K := PV_RunJoin_FixtureRecords.M) s0
  have he : out = s1 := PV_RunJoin_NullifierPermutation17.state_injective out s1 hc canon1 (by
    rw [show liftA (K := PV_RunJoin_FixtureRecords.M) out = _ from funext hm,lift0,lift1]
    exact PV_RunJoin_PathModel16.round_10_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_PathModel16.round_10_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_PathModel16.round_10_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_PathModel16.round_10_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_PathModel16.round_10_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_PathModel16.round_10_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_PathModel16.round_10_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_PathModel16.round_10_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_PathModel16.round_10_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_PathModel16.round_10_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_PathModel16.round_10_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_PathModel16.round_10_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_PathModel16.round_10_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_PathModel16.round_10_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_PathModel16.round_10_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_PathModel16.round_10_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_PathModel16.round_10_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_PathModel16.round_10_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_PathModel16.round_10_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_PathModel16.round_10_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_PathModel16.round_10_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_PathModel16.round_10_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_PathModel16.round_10_23
#print axioms step21
theorem pair0 : poseidon2.evaluate_trace_round_pair s0 0#usize = ok (some (s2,s3)) := by
  apply PV_RunJoin_IndexedPair19.source s0 s1 s2 s3 0#usize (by decide)
  · rw [if_pos rfl]; exact external
  · have hi : Usize.wrapping_mul 2#usize 0#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step0
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 0#usize) 1#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step1
#print axioms pair0
theorem pair1 : poseidon2.evaluate_trace_round_pair s3 1#usize = ok (some (s4,s5)) := by
  apply PV_RunJoin_IndexedPair19.source s3 s3 s4 s5 1#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 1#usize = 2#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step2
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 1#usize) 1#usize = 3#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step3
#print axioms pair1
theorem pair2 : poseidon2.evaluate_trace_round_pair s5 2#usize = ok (some (s6,s7)) := by
  apply PV_RunJoin_IndexedPair19.source s5 s5 s6 s7 2#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 2#usize = 4#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step4
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 2#usize) 1#usize = 5#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step5
#print axioms pair2
theorem pair3 : poseidon2.evaluate_trace_round_pair s7 3#usize = ok (some (s8,s9)) := by
  apply PV_RunJoin_IndexedPair19.source s7 s7 s8 s9 3#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 3#usize = 6#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step6
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 3#usize) 1#usize = 7#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step7
#print axioms pair3
theorem pair4 : poseidon2.evaluate_trace_round_pair s9 4#usize = ok (some (s10,s11)) := by
  apply PV_RunJoin_IndexedPair19.source s9 s9 s10 s11 4#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 4#usize = 8#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step8
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 4#usize) 1#usize = 9#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step9
#print axioms pair4
theorem pair5 : poseidon2.evaluate_trace_round_pair s11 5#usize = ok (some (s12,s13)) := by
  apply PV_RunJoin_IndexedPair19.source s11 s11 s12 s13 5#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 5#usize = 10#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step10
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 5#usize) 1#usize = 11#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step11
#print axioms pair5
theorem pair6 : poseidon2.evaluate_trace_round_pair s13 6#usize = ok (some (s14,s15)) := by
  apply PV_RunJoin_IndexedPair19.source s13 s13 s14 s15 6#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 6#usize = 12#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step12
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 6#usize) 1#usize = 13#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step13
#print axioms pair6
theorem pair7 : poseidon2.evaluate_trace_round_pair s15 7#usize = ok (some (s16,s17)) := by
  apply PV_RunJoin_IndexedPair19.source s15 s15 s16 s17 7#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 7#usize = 14#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step14
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 7#usize) 1#usize = 15#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step15
#print axioms pair7
theorem pair8 : poseidon2.evaluate_trace_round_pair s17 8#usize = ok (some (s18,s19)) := by
  apply PV_RunJoin_IndexedPair19.source s17 s17 s18 s19 8#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 8#usize = 16#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step16
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 8#usize) 1#usize = 17#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step17
#print axioms pair8
theorem pair9 : poseidon2.evaluate_trace_round_pair s19 9#usize = ok (some (s20,s21)) := by
  apply PV_RunJoin_IndexedPair19.source s19 s19 s20 s21 9#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 9#usize = 18#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step18
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 9#usize) 1#usize = 19#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step19
#print axioms pair9
theorem pair10 : poseidon2.evaluate_trace_round_pair s21 10#usize = ok (some (s22,s23)) := by
  apply PV_RunJoin_IndexedPair19.source s21 s21 s22 s23 10#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 10#usize = 20#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step20
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 10#usize) 1#usize = 21#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step21
#print axioms pair10
end R1Z.PV_RunJoin_ValidatorCell1019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell1119
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,896398700#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_PathModel16.s_11_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [94129108#u32,573462244#u32,682195655#u32,2111470635#u32,119935125#u32,426164480#u32,1847017005#u32,767561947#u32,1868356049#u32,698554533#u32,1223230467#u32,1690343972#u32,816835507#u32,1794517638#u32,216151536#u32,1734786059#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_PathModel16.s_11_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1084917151#u32,787064043#u32,871498967#u32,557232469#u32,420273303#u32,322958260#u32,176002498#u32,268379993#u32,773472982#u32,364544378#u32,2123045026#u32,2060838034#u32,1005964624#u32,448767443#u32,481368203#u32,1411901591#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_PathModel16.s_11_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [700999455#u32,1345127095#u32,82444269#u32,290870676#u32,2013246905#u32,2033235893#u32,1463266857#u32,1772345072#u32,1376388505#u32,1254515783#u32,1615536886#u32,742870271#u32,1878379352#u32,1526847898#u32,1049551815#u32,509253762#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_PathModel16.s_11_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [928104648#u32,365659735#u32,2066294698#u32,1166007295#u32,1725005902#u32,1131109242#u32,309395#u32,1407558190#u32,863201534#u32,905511032#u32,613962967#u32,1441382024#u32,376940428#u32,733626298#u32,1708500417#u32,1854315712#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_PathModel16.s_11_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [1403810704#u32,1990556179#u32,1759848204#u32,1532759232#u32,846162112#u32,1948780769#u32,1994554782#u32,887428198#u32,404672731#u32,688507236#u32,477506246#u32,1423307291#u32,2116457267#u32,1096348007#u32,510785228#u32,1730177042#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_PathModel16.s_11_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [367829393#u32,1783722188#u32,1165378770#u32,1629235643#u32,120011964#u32,908887255#u32,1341893270#u32,753995859#u32,51668049#u32,2104843018#u32,1280774044#u32,1389211987#u32,1175615042#u32,805689189#u32,1863456042#u32,1539228921#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_PathModel16.s_11_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [655676628#u32,448046043#u32,995081395#u32,886299133#u32,1771903214#u32,321618053#u32,802719202#u32,1822902244#u32,982866833#u32,633224713#u32,211920241#u32,192441704#u32,2133558418#u32,641501969#u32,989372960#u32,1969023627#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_PathModel16.s_11_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [2115062442#u32,20655688#u32,1562772435#u32,970322530#u32,862933475#u32,423531199#u32,1637303992#u32,274236323#u32,825512743#u32,616862648#u32,1830571729#u32,1834814427#u32,1461250615#u32,155901323#u32,932627813#u32,1360164134#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_PathModel16.s_11_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [689419265#u32,952871160#u32,1910276695#u32,518538298#u32,1393232331#u32,1266263715#u32,1786335688#u32,1303470968#u32,1371147873#u32,2082747129#u32,684442137#u32,139343964#u32,1423405174#u32,1861435221#u32,440611399#u32,750197973#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_PathModel16.s_11_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1213425299#u32,1148346959#u32,1868545542#u32,122145344#u32,603916212#u32,1128342416#u32,1523642993#u32,2013239165#u32,1756228136#u32,802796367#u32,984555165#u32,1865185888#u32,2041941644#u32,1534865616#u32,617239450#u32,679219909#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_PathModel16.s_11_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [880625932#u32,1140920640#u32,1582181118#u32,481155057#u32,528936083#u32,866183161#u32,1504509223#u32,2138345068#u32,1451475801#u32,1497497168#u32,1007232198#u32,1194638550#u32,828394846#u32,197319855#u32,693883835#u32,307494889#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_PathModel16.s_11_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [701733339#u32,1214751227#u32,1090709176#u32,1998450815#u32,10351957#u32,1047859281#u32,973485489#u32,1636445178#u32,1179139473#u32,1181016429#u32,687450779#u32,1345583521#u32,236084499#u32,999446172#u32,1849965078#u32,72332643#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_PathModel16.s_11_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1128184911#u32,1067938692#u32,2034605817#u32,1404539784#u32,2083486768#u32,1586550432#u32,939952055#u32,1506463801#u32,459184719#u32,1545682709#u32,1575632592#u32,920251279#u32,1122120973#u32,216461138#u32,340475853#u32,748870184#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_PathModel16.s_11_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1636779915#u32,175854017#u32,1029643312#u32,431107167#u32,743423940#u32,870402120#u32,1269093674#u32,1032318121#u32,2048984535#u32,1813181428#u32,1942954283#u32,1770837271#u32,292916981#u32,111699120#u32,1790603911#u32,620509058#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_PathModel16.s_11_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [511138255#u32,1487002580#u32,1222951540#u32,888093584#u32,816089142#u32,205196954#u32,1119956838#u32,807515250#u32,1588164109#u32,1629126379#u32,178993586#u32,460851013#u32,339569#u32,1733463399#u32,124417230#u32,94950412#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_PathModel16.s_11_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [924469829#u32,1654435804#u32,465852657#u32,1572323913#u32,253695419#u32,1303100841#u32,1646313688#u32,308801696#u32,1588976358#u32,611958730#u32,920755293#u32,175056759#u32,801698825#u32,760530865#u32,1147263858#u32,1577508697#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_PathModel16.s_11_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [204026897#u32,962184655#u32,239454165#u32,1302077209#u32,1337312203#u32,830009484#u32,450179339#u32,1891188219#u32,833259857#u32,1350361147#u32,1563331497#u32,1228179264#u32,1967014372#u32,145321117#u32,1148607060#u32,907465216#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_PathModel16.s_11_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1868382988#u32,1340920217#u32,857643892#u32,1292077104#u32,339814951#u32,773985424#u32,1899572528#u32,1155697346#u32,1809298555#u32,326322027#u32,1354871475#u32,1594299632#u32,1590667545#u32,1908035614#u32,1136480320#u32,1754494967#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_PathModel16.s_11_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [880173390#u32,74404375#u32,448771942#u32,1754308927#u32,1452003766#u32,379832707#u32,1537746585#u32,1831153951#u32,542948969#u32,667544484#u32,994922243#u32,634489950#u32,698726449#u32,1217018202#u32,1554170938#u32,746213796#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_PathModel16.s_11_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [861837123#u32,1263206271#u32,1777033300#u32,341903854#u32,1216294806#u32,438906666#u32,2079750619#u32,1001291528#u32,1067867817#u32,494171386#u32,1006619292#u32,335048057#u32,723931452#u32,970223232#u32,1216954517#u32,230692318#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_PathModel16.s_11_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [5038921#u32,1956531732#u32,2004418039#u32,218416323#u32,141496826#u32,576480232#u32,175009132#u32,719297448#u32,982637873#u32,1395726175#u32,1325133274#u32,1520938454#u32,2055002852#u32,1757939830#u32,1571462092#u32,295203270#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_PathModel16.s_11_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [846534105#u32,1820801376#u32,528175218#u32,1207453780#u32,1384645225#u32,2146332188#u32,1402071618#u32,2092064373#u32,111938116#u32,178817203#u32,349519494#u32,1917116816#u32,926601591#u32,1406468899#u32,687786511#u32,1397337710#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_PathModel16.s_11_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,1763090787#u32,852145833#u32,507382756#u32,516029509#u32,751932278#u32,1683938262#u32,220085100#u32,932405928#u32,1776313439#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_PathModel16.s_11_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift23
theorem canon23 : Canonical s23 := by
  intro i
  fin_cases i <;> decide
#print axioms canon23
theorem external : poseidon2.external_linear_lazy s0 = ok s1 := by
  obtain ⟨out,ho,hc,hm⟩ := PV_Src_ExternalModel.source (K := PV_RunJoin_FixtureRecords.M) s0
  have he : out = s1 := PV_RunJoin_NullifierPermutation17.state_injective out s1 hc canon1 (by
    rw [show liftA (K := PV_RunJoin_FixtureRecords.M) out = _ from funext hm,lift0,lift1]
    exact PV_RunJoin_PathModel16.round_11_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_PathModel16.round_11_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_PathModel16.round_11_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_PathModel16.round_11_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_PathModel16.round_11_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_PathModel16.round_11_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_PathModel16.round_11_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_PathModel16.round_11_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_PathModel16.round_11_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_PathModel16.round_11_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_PathModel16.round_11_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_PathModel16.round_11_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_PathModel16.round_11_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_PathModel16.round_11_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_PathModel16.round_11_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_PathModel16.round_11_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_PathModel16.round_11_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_PathModel16.round_11_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_PathModel16.round_11_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_PathModel16.round_11_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_PathModel16.round_11_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_PathModel16.round_11_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_PathModel16.round_11_23
#print axioms step21
theorem pair0 : poseidon2.evaluate_trace_round_pair s0 0#usize = ok (some (s2,s3)) := by
  apply PV_RunJoin_IndexedPair19.source s0 s1 s2 s3 0#usize (by decide)
  · rw [if_pos rfl]; exact external
  · have hi : Usize.wrapping_mul 2#usize 0#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step0
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 0#usize) 1#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step1
#print axioms pair0
theorem pair1 : poseidon2.evaluate_trace_round_pair s3 1#usize = ok (some (s4,s5)) := by
  apply PV_RunJoin_IndexedPair19.source s3 s3 s4 s5 1#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 1#usize = 2#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step2
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 1#usize) 1#usize = 3#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step3
#print axioms pair1
theorem pair2 : poseidon2.evaluate_trace_round_pair s5 2#usize = ok (some (s6,s7)) := by
  apply PV_RunJoin_IndexedPair19.source s5 s5 s6 s7 2#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 2#usize = 4#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step4
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 2#usize) 1#usize = 5#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step5
#print axioms pair2
theorem pair3 : poseidon2.evaluate_trace_round_pair s7 3#usize = ok (some (s8,s9)) := by
  apply PV_RunJoin_IndexedPair19.source s7 s7 s8 s9 3#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 3#usize = 6#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step6
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 3#usize) 1#usize = 7#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step7
#print axioms pair3
theorem pair4 : poseidon2.evaluate_trace_round_pair s9 4#usize = ok (some (s10,s11)) := by
  apply PV_RunJoin_IndexedPair19.source s9 s9 s10 s11 4#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 4#usize = 8#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step8
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 4#usize) 1#usize = 9#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step9
#print axioms pair4
theorem pair5 : poseidon2.evaluate_trace_round_pair s11 5#usize = ok (some (s12,s13)) := by
  apply PV_RunJoin_IndexedPair19.source s11 s11 s12 s13 5#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 5#usize = 10#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step10
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 5#usize) 1#usize = 11#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step11
#print axioms pair5
theorem pair6 : poseidon2.evaluate_trace_round_pair s13 6#usize = ok (some (s14,s15)) := by
  apply PV_RunJoin_IndexedPair19.source s13 s13 s14 s15 6#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 6#usize = 12#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step12
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 6#usize) 1#usize = 13#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step13
#print axioms pair6
theorem pair7 : poseidon2.evaluate_trace_round_pair s15 7#usize = ok (some (s16,s17)) := by
  apply PV_RunJoin_IndexedPair19.source s15 s15 s16 s17 7#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 7#usize = 14#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step14
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 7#usize) 1#usize = 15#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step15
#print axioms pair7
theorem pair8 : poseidon2.evaluate_trace_round_pair s17 8#usize = ok (some (s18,s19)) := by
  apply PV_RunJoin_IndexedPair19.source s17 s17 s18 s19 8#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 8#usize = 16#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step16
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 8#usize) 1#usize = 17#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step17
#print axioms pair8
theorem pair9 : poseidon2.evaluate_trace_round_pair s19 9#usize = ok (some (s20,s21)) := by
  apply PV_RunJoin_IndexedPair19.source s19 s19 s20 s21 9#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 9#usize = 18#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step18
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 9#usize) 1#usize = 19#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step19
#print axioms pair9
theorem pair10 : poseidon2.evaluate_trace_round_pair s21 10#usize = ok (some (s22,s23)) := by
  apply PV_RunJoin_IndexedPair19.source s21 s21 s22 s23 10#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 10#usize = 20#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step20
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 10#usize) 1#usize = 21#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step21
#print axioms pair10
end R1Z.PV_RunJoin_ValidatorCell1119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell1219
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,2203#u32,2220#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_PathModel16.s_12_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [1464525294#u32,1461756779#u32,1427942716#u32,89339795#u32,1464525770#u32,1461757255#u32,1427943192#u32,89340271#u32,1172278983#u32,1055384581#u32,1646963972#u32,255012556#u32,1073738561#u32,1182327163#u32,489305328#u32,12932053#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_PathModel16.s_12_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1967179283#u32,1532661074#u32,588667167#u32,1850985539#u32,1497798336#u32,449642746#u32,871545247#u32,1089841003#u32,162492569#u32,1943022493#u32,698261418#u32,1089729765#u32,249455999#u32,762615734#u32,1805259828#u32,1682777138#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_PathModel16.s_12_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [575011623#u32,1625402890#u32,498865820#u32,198168781#u32,500927916#u32,282078065#u32,893105189#u32,1433418126#u32,641002647#u32,1872182145#u32,1387080494#u32,1216526177#u32,1666535306#u32,359559958#u32,675637367#u32,1868142987#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_PathModel16.s_12_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [736252918#u32,1516349177#u32,518557060#u32,1665612511#u32,102085712#u32,178848378#u32,1345131896#u32,1782266630#u32,1723229500#u32,2000200296#u32,1283870591#u32,895491140#u32,1187890653#u32,953373684#u32,128894427#u32,922422203#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_PathModel16.s_12_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [150066442#u32,1234806161#u32,1506338596#u32,1811525307#u32,1400779908#u32,1348384911#u32,28714467#u32,335896358#u32,486290120#u32,272564390#u32,1290598316#u32,179278273#u32,666292938#u32,2051414670#u32,410119247#u32,1841513171#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_PathModel16.s_12_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [748819468#u32,150249301#u32,1928120332#u32,1866577074#u32,1531747816#u32,1162248893#u32,1981789731#u32,1085457229#u32,1031036384#u32,2119933923#u32,1933159466#u32,947325721#u32,431244209#u32,1174320870#u32,897749557#u32,36623690#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_PathModel16.s_12_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [591267090#u32,1754412251#u32,1165436320#u32,480536658#u32,973243596#u32,872792415#u32,596924932#u32,206465255#u32,432833988#u32,993884547#u32,1179533600#u32,1347366037#u32,1746123763#u32,223819910#u32,683166473#u32,887593444#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_PathModel16.s_12_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1774406006#u32,1298468859#u32,1874929248#u32,1466203240#u32,887554435#u32,623833366#u32,1465785256#u32,2020414693#u32,1259715897#u32,575430294#u32,500653394#u32,1469855017#u32,1548834084#u32,854876619#u32,173507544#u32,2125939950#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_PathModel16.s_12_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1551482606#u32,1679251693#u32,1983157683#u32,1950628500#u32,1038767373#u32,1772182102#u32,41270792#u32,838304366#u32,563144125#u32,1662050102#u32,1948750304#u32,1510269925#u32,1096212486#u32,790962796#u32,1486771017#u32,1537295968#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_PathModel16.s_12_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [38654088#u32,636446776#u32,776026802#u32,317258142#u32,824883126#u32,1542304951#u32,277860427#u32,1069066979#u32,172682732#u32,1387742736#u32,1612681963#u32,269904523#u32,500752288#u32,175318749#u32,1803347944#u32,137938573#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_PathModel16.s_12_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [1134605070#u32,1035438658#u32,1951045486#u32,1668024450#u32,555605949#u32,1453550981#u32,700590958#u32,99801834#u32,1027545108#u32,1326330543#u32,370397451#u32,2121323532#u32,867969408#u32,1635739459#u32,196906375#u32,1582641787#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_PathModel16.s_12_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [938550667#u32,1070457244#u32,1789625911#u32,264665445#u32,184898884#u32,1816997812#u32,979092772#u32,2127368668#u32,564289943#u32,273221368#u32,1364886538#u32,257369896#u32,122053705#u32,1541883929#u32,1222238998#u32,881988612#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_PathModel16.s_12_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [88045408#u32,1987203875#u32,201031159#u32,1975408411#u32,248454056#u32,2071424212#u32,35460630#u32,1776871622#u32,131415337#u32,2141940135#u32,548707346#u32,689369970#u32,53318489#u32,145416059#u32,674216545#u32,1252580011#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_PathModel16.s_12_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1358142914#u32,577409264#u32,1139751354#u32,49388092#u32,577837837#u32,1668221723#u32,1872429196#u32,640839553#u32,378982996#u32,1466033611#u32,2120779473#u32,456090351#u32,1583570583#u32,1675035169#u32,153675260#u32,111399710#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_PathModel16.s_12_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [2020526694#u32,1729967150#u32,1284576947#u32,1350110254#u32,1480293288#u32,2074301690#u32,940750042#u32,1364099985#u32,270257493#u32,647524077#u32,1724771121#u32,987862692#u32,814062295#u32,87758122#u32,934325351#u32,399552646#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_PathModel16.s_12_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [870601770#u32,827536981#u32,1666723725#u32,203043553#u32,202497900#u32,74142166#u32,1284283764#u32,500622991#u32,1478274230#u32,1654976371#u32,31639901#u32,1671448962#u32,2106650183#u32,260080836#u32,543799767#u32,2059153863#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_PathModel16.s_12_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [1511455681#u32,528544275#u32,886971097#u32,513181506#u32,1320990494#u32,887281950#u32,2143382096#u32,1676107660#u32,2089031445#u32,320679811#u32,2035494860#u32,1925572657#u32,200719138#u32,257868670#u32,1259953191#u32,536195382#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_PathModel16.s_12_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1003998675#u32,476239359#u32,1721637278#u32,2000421108#u32,1925684448#u32,1259304402#u32,1963929099#u32,1991886621#u32,1055747816#u32,437348114#u32,1235294134#u32,1533346372#u32,1413883625#u32,767650715#u32,720744197#u32,773333975#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_PathModel16.s_12_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [464398735#u32,2057521151#u32,729589054#u32,993031636#u32,1954371847#u32,255315754#u32,2503550#u32,213006716#u32,1425532479#u32,1873249332#u32,1654606925#u32,778354029#u32,589145874#u32,958875873#u32,901979382#u32,35114545#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_PathModel16.s_12_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1112156917#u32,1695029182#u32,830294893#u32,1552538129#u32,1448730322#u32,626408049#u32,744691787#u32,1472051807#u32,927240281#u32,74729131#u32,202370388#u32,1351245481#u32,1353558417#u32,1360280877#u32,249013703#u32,445186330#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_PathModel16.s_12_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1486258219#u32,16540923#u32,1355800072#u32,1730569551#u32,3390742#u32,752171773#u32,1484482243#u32,1136166535#u32,976677382#u32,1896649249#u32,1732959350#u32,23373106#u32,2084064459#u32,1181262332#u32,1770278059#u32,1609880159#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_PathModel16.s_12_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [685921978#u32,744031214#u32,19670332#u32,896558227#u32,1654818387#u32,1930371725#u32,2789989#u32,1749488261#u32,1406151491#u32,1374935975#u32,39630836#u32,752164871#u32,460682416#u32,1216664923#u32,1514109#u32,1659852638#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_PathModel16.s_12_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,1224545956#u32,757035799#u32,546245171#u32,158832750#u32,45012311#u32,1749646592#u32,235891802#u32,1021820704#u32,62834274#u32,1483589884#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_PathModel16.s_12_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift23
theorem canon23 : Canonical s23 := by
  intro i
  fin_cases i <;> decide
#print axioms canon23
theorem external : poseidon2.external_linear_lazy s0 = ok s1 := by
  obtain ⟨out,ho,hc,hm⟩ := PV_Src_ExternalModel.source (K := PV_RunJoin_FixtureRecords.M) s0
  have he : out = s1 := PV_RunJoin_NullifierPermutation17.state_injective out s1 hc canon1 (by
    rw [show liftA (K := PV_RunJoin_FixtureRecords.M) out = _ from funext hm,lift0,lift1]
    exact PV_RunJoin_PathModel16.round_12_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_PathModel16.round_12_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_PathModel16.round_12_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_PathModel16.round_12_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_PathModel16.round_12_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_PathModel16.round_12_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_PathModel16.round_12_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_PathModel16.round_12_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_PathModel16.round_12_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_PathModel16.round_12_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_PathModel16.round_12_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_PathModel16.round_12_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_PathModel16.round_12_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_PathModel16.round_12_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_PathModel16.round_12_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_PathModel16.round_12_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_PathModel16.round_12_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_PathModel16.round_12_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_PathModel16.round_12_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_PathModel16.round_12_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_PathModel16.round_12_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_PathModel16.round_12_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_PathModel16.round_12_23
#print axioms step21
theorem pair0 : poseidon2.evaluate_trace_round_pair s0 0#usize = ok (some (s2,s3)) := by
  apply PV_RunJoin_IndexedPair19.source s0 s1 s2 s3 0#usize (by decide)
  · rw [if_pos rfl]; exact external
  · have hi : Usize.wrapping_mul 2#usize 0#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step0
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 0#usize) 1#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step1
#print axioms pair0
theorem pair1 : poseidon2.evaluate_trace_round_pair s3 1#usize = ok (some (s4,s5)) := by
  apply PV_RunJoin_IndexedPair19.source s3 s3 s4 s5 1#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 1#usize = 2#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step2
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 1#usize) 1#usize = 3#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step3
#print axioms pair1
theorem pair2 : poseidon2.evaluate_trace_round_pair s5 2#usize = ok (some (s6,s7)) := by
  apply PV_RunJoin_IndexedPair19.source s5 s5 s6 s7 2#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 2#usize = 4#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step4
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 2#usize) 1#usize = 5#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step5
#print axioms pair2
theorem pair3 : poseidon2.evaluate_trace_round_pair s7 3#usize = ok (some (s8,s9)) := by
  apply PV_RunJoin_IndexedPair19.source s7 s7 s8 s9 3#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 3#usize = 6#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step6
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 3#usize) 1#usize = 7#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step7
#print axioms pair3
theorem pair4 : poseidon2.evaluate_trace_round_pair s9 4#usize = ok (some (s10,s11)) := by
  apply PV_RunJoin_IndexedPair19.source s9 s9 s10 s11 4#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 4#usize = 8#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step8
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 4#usize) 1#usize = 9#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step9
#print axioms pair4
theorem pair5 : poseidon2.evaluate_trace_round_pair s11 5#usize = ok (some (s12,s13)) := by
  apply PV_RunJoin_IndexedPair19.source s11 s11 s12 s13 5#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 5#usize = 10#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step10
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 5#usize) 1#usize = 11#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step11
#print axioms pair5
theorem pair6 : poseidon2.evaluate_trace_round_pair s13 6#usize = ok (some (s14,s15)) := by
  apply PV_RunJoin_IndexedPair19.source s13 s13 s14 s15 6#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 6#usize = 12#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step12
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 6#usize) 1#usize = 13#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step13
#print axioms pair6
theorem pair7 : poseidon2.evaluate_trace_round_pair s15 7#usize = ok (some (s16,s17)) := by
  apply PV_RunJoin_IndexedPair19.source s15 s15 s16 s17 7#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 7#usize = 14#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step14
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 7#usize) 1#usize = 15#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step15
#print axioms pair7
theorem pair8 : poseidon2.evaluate_trace_round_pair s17 8#usize = ok (some (s18,s19)) := by
  apply PV_RunJoin_IndexedPair19.source s17 s17 s18 s19 8#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 8#usize = 16#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step16
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 8#usize) 1#usize = 17#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step17
#print axioms pair8
theorem pair9 : poseidon2.evaluate_trace_round_pair s19 9#usize = ok (some (s20,s21)) := by
  apply PV_RunJoin_IndexedPair19.source s19 s19 s20 s21 9#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 9#usize = 18#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step18
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 9#usize) 1#usize = 19#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step19
#print axioms pair9
theorem pair10 : poseidon2.evaluate_trace_round_pair s21 10#usize = ok (some (s22,s23)) := by
  apply PV_RunJoin_IndexedPair19.source s21 s21 s22 s23 10#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 10#usize = 20#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step20
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 10#usize) 1#usize = 21#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step21
#print axioms pair10
end R1Z.PV_RunJoin_ValidatorCell1219
