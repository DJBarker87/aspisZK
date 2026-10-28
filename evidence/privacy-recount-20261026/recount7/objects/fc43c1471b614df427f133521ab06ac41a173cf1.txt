import R1Z.PV_RunJoin_IndexedPair19
import R1Z.PV_RunJoin_PathCell2816
import R1Z.PV_RunJoin_PathCell2916
import R1Z.PV_RunJoin_OutputRecipient16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell2819
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,2111428769#u32,132405182#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_PathModel16.s_28_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [1288934751#u32,1280729488#u32,1414565052#u32,944898359#u32,1228168909#u32,1827131924#u32,2127677108#u32,1445577459#u32,488564111#u32,1401311329#u32,1560918867#u32,811675735#u32,1584527216#u32,349790787#u32,553839936#u32,856117822#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_PathModel16.s_28_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [2091716331#u32,1905471989#u32,1122849752#u32,1235412452#u32,1834899254#u32,445781113#u32,1025986245#u32,675250048#u32,1051835334#u32,2061828665#u32,2065302038#u32,338789354#u32,2024757870#u32,100597788#u32,743400964#u32,904912012#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_PathModel16.s_28_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [342372688#u32,803146619#u32,517564993#u32,269161897#u32,170768739#u32,1895403295#u32,1203318385#u32,991876513#u32,518496590#u32,1006855786#u32,2078037762#u32,1990411184#u32,1728030447#u32,1680002371#u32,863808133#u32,1869975732#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_PathModel16.s_28_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [1957052340#u32,1108774621#u32,1896394567#u32,1493005291#u32,951377550#u32,1019510304#u32,1502316223#u32,476728063#u32,13003161#u32,1441018536#u32,522604155#u32,341307362#u32,822566312#u32,1655086600#u32,598878112#u32,512970854#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_PathModel16.s_28_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [1353452742#u32,1381448647#u32,7070719#u32,516499998#u32,1258747341#u32,1402382159#u32,66375902#u32,1814047653#u32,27007205#u32,1442778225#u32,1236675268#u32,1092789024#u32,1669428512#u32,1007595416#u32,186558498#u32,1431115132#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_PathModel16.s_28_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [1055572189#u32,1489628445#u32,122321236#u32,26696143#u32,1588223938#u32,1071457872#u32,84725015#u32,243112652#u32,1417618391#u32,92218114#u32,1595786147#u32,816101754#u32,890686006#u32,844681053#u32,1518582900#u32,468671472#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_PathModel16.s_28_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [869749571#u32,1538581033#u32,293595060#u32,155737160#u32,2017325857#u32,12409364#u32,612669421#u32,575776787#u32,1115480288#u32,34469655#u32,2046395396#u32,1317182240#u32,1546764881#u32,918703672#u32,1629835151#u32,1591422186#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_PathModel16.s_28_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1944770730#u32,341735547#u32,1537828281#u32,1573586801#u32,2056859488#u32,1149187985#u32,1228706810#u32,1293130530#u32,1998194323#u32,1184935253#u32,515484193#u32,1650171937#u32,1895026013#u32,1278718386#u32,1618048886#u32,1704219655#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_PathModel16.s_28_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [230218220#u32,1360996210#u32,1947433578#u32,871156926#u32,294267391#u32,78915600#u32,1683172937#u32,27752350#u32,1237580014#u32,1567491204#u32,594097133#u32,1992477506#u32,913074996#u32,690836755#u32,2021396328#u32,281573920#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_PathModel16.s_28_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1856896647#u32,563774201#u32,950161500#u32,539922048#u32,1556917119#u32,465427591#u32,1524704447#u32,978928391#u32,846713552#u32,1048567873#u32,1967853729#u32,2100267614#u32,1575086369#u32,633352221#u32,1479529474#u32,1251704087#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_PathModel16.s_28_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [644212396#u32,525643885#u32,1862192684#u32,2121557876#u32,1679788401#u32,966260199#u32,1507771754#u32,336260945#u32,967021990#u32,2107272944#u32,704427294#u32,1986010393#u32,987653356#u32,163676244#u32,1740342691#u32,2060567210#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_PathModel16.s_28_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [758570230#u32,545263741#u32,1596521577#u32,2063400419#u32,573025182#u32,447397511#u32,1023675750#u32,65483866#u32,1391866697#u32,463098123#u32,1946147167#u32,50134748#u32,1305013959#u32,1631610096#u32,1140672459#u32,1138120115#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_PathModel16.s_28_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1886950326#u32,1503888824#u32,2004184590#u32,622292171#u32,1247859245#u32,1674534318#u32,1503994378#u32,854625213#u32,876419598#u32,1400143986#u32,948499675#u32,152122779#u32,1459382445#u32,1382000091#u32,1560885560#u32,248970472#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_PathModel16.s_28_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [809094588#u32,1214662574#u32,1571659283#u32,52458787#u32,1103713122#u32,733519074#u32,593953612#u32,719696207#u32,223332650#u32,1665348764#u32,311832506#u32,35418904#u32,2077783988#u32,1480174373#u32,190783231#u32,1806360483#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_PathModel16.s_28_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [252130872#u32,606639407#u32,387811752#u32,1749295628#u32,1779230868#u32,390863782#u32,1218623241#u32,355377494#u32,61268622#u32,519498311#u32,880883221#u32,586403268#u32,1790504054#u32,1183562141#u32,1799477471#u32,996549846#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_PathModel16.s_28_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [894139708#u32,407190500#u32,576174597#u32,355282664#u32,1149496155#u32,1759404311#u32,141789159#u32,1069874239#u32,1200483768#u32,1795616242#u32,2029321304#u32,821619475#u32,296452451#u32,1652820474#u32,1619825142#u32,418585985#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_PathModel16.s_28_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [631584348#u32,298708026#u32,1043866720#u32,1312648182#u32,497552178#u32,124699091#u32,133803320#u32,1791475765#u32,1082100893#u32,7775020#u32,1299846173#u32,138012277#u32,1773475008#u32,2080858519#u32,1115951330#u32,386523708#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_PathModel16.s_28_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [752414019#u32,2098566310#u32,1740108077#u32,608000071#u32,1485308414#u32,1647560093#u32,1786597230#u32,490190306#u32,722335533#u32,1642779757#u32,1402478296#u32,162462068#u32,232768218#u32,1135453808#u32,1941498608#u32,1300485760#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_PathModel16.s_28_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [403023937#u32,1981505472#u32,1215671669#u32,167455799#u32,1027988239#u32,474096886#u32,1219475700#u32,1190347688#u32,90565#u32,1675245789#u32,1501638070#u32,1755122767#u32,1902186129#u32,1654779120#u32,1853767378#u32,1334208033#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_PathModel16.s_28_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1527224494#u32,1361982627#u32,579464894#u32,1001292247#u32,1676880695#u32,1849814208#u32,1080616484#u32,2040025738#u32,1246486238#u32,369574920#u32,843086591#u32,451575756#u32,145673779#u32,1330645073#u32,1408990895#u32,1943412493#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_PathModel16.s_28_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [952550792#u32,2083944263#u32,1375806039#u32,398219260#u32,206141707#u32,1258162853#u32,668679014#u32,1753378663#u32,488591165#u32,101398497#u32,88783697#u32,376940220#u32,1634208227#u32,612207940#u32,349246334#u32,1514292727#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_PathModel16.s_28_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1559847425#u32,1588208959#u32,1492957689#u32,1730659095#u32,1415104067#u32,310312333#u32,265132840#u32,2065292189#u32,595512952#u32,1222170474#u32,1529722723#u32,2021907645#u32,2041775746#u32,106912769#u32,121881637#u32,210856507#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_PathModel16.s_28_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,1368876468#u32,1821041711#u32,705652978#u32,1921364862#u32,274763192#u32,1464737902#u32,874124749#u32,189671234#u32,786198476#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_PathModel16.s_28_23 := by
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
    exact PV_RunJoin_PathModel16.round_28_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_PathModel16.round_28_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_PathModel16.round_28_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_PathModel16.round_28_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_PathModel16.round_28_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_PathModel16.round_28_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_PathModel16.round_28_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_PathModel16.round_28_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_PathModel16.round_28_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_PathModel16.round_28_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_PathModel16.round_28_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_PathModel16.round_28_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_PathModel16.round_28_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_PathModel16.round_28_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_PathModel16.round_28_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_PathModel16.round_28_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_PathModel16.round_28_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_PathModel16.round_28_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_PathModel16.round_28_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_PathModel16.round_28_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_PathModel16.round_28_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_PathModel16.round_28_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_PathModel16.round_28_23
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
end R1Z.PV_RunJoin_ValidatorCell2819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell2919
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,3303#u32,3320#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_PathModel16.s_29_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [828184911#u32,1089151082#u32,147957552#u32,1905452677#u32,828185387#u32,1089151558#u32,147958028#u32,1905453153#u32,404924219#u32,512013462#u32,418834697#u32,16579720#u32,2079517323#u32,607842691#u32,24924258#u32,1404697741#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_PathModel16.s_29_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [621272862#u32,157771672#u32,1520132771#u32,1253507779#u32,1040408793#u32,386579697#u32,1967880535#u32,2084120338#u32,1377043696#u32,605255300#u32,2047579268#u32,65659693#u32,887075507#u32,72308631#u32,1098866032#u32,1147042454#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_PathModel16.s_29_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [875791967#u32,1852020584#u32,1286466911#u32,1821073609#u32,6685670#u32,125395869#u32,1756189402#u32,1391188642#u32,80457386#u32,1405741667#u32,487716641#u32,1358558524#u32,1083282393#u32,720562084#u32,1249826256#u32,124683763#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_PathModel16.s_29_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [595767128#u32,1433893293#u32,397768684#u32,1995166472#u32,463944354#u32,1933945342#u32,1708300106#u32,1791994001#u32,1955248726#u32,1127754107#u32,54993913#u32,2135240867#u32,109515883#u32,1902613827#u32,735571711#u32,278907712#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_PathModel16.s_29_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [745991823#u32,1468484286#u32,1417068998#u32,1706057780#u32,868262732#u32,1635695674#u32,489453253#u32,646623755#u32,1387805976#u32,1548160247#u32,762966306#u32,217603301#u32,14055960#u32,902453637#u32,873241390#u32,881661429#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_PathModel16.s_29_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [669519056#u32,373383620#u32,1739037330#u32,1434163160#u32,1556033896#u32,1453710001#u32,1682501548#u32,1634114008#u32,450405208#u32,96931518#u32,645832817#u32,1149790372#u32,234690363#u32,1427861994#u32,206654226#u32,1420787743#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_PathModel16.s_29_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [1883461436#u32,1584430381#u32,394154127#u32,505248460#u32,774416047#u32,848086660#u32,1364005122#u32,567644570#u32,880854916#u32,255711605#u32,1118888093#u32,1320772602#u32,1796636392#u32,615106039#u32,1840785338#u32,1213121736#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_PathModel16.s_29_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1446347041#u32,233036458#u32,1584397978#u32,669599917#u32,548967159#u32,1480574402#u32,1494580688#u32,618120205#u32,1876369328#u32,1833751194#u32,1928713105#u32,1169360723#u32,2135980097#u32,552677329#u32,1129368372#u32,1950084633#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_PathModel16.s_29_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [443845399#u32,1693132236#u32,333924440#u32,1991011799#u32,1556865756#u32,1526966093#u32,2042037560#u32,217599605#u32,1117201298#u32,601482749#u32,777360058#u32,125600729#u32,1712294646#u32,586914715#u32,1017220723#u32,1159803802#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_PathModel16.s_29_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [847633868#u32,1552076081#u32,526792725#u32,1380540100#u32,1576451658#u32,668081216#u32,779636355#u32,900416683#u32,1126789287#u32,1367188652#u32,1306693847#u32,1070938196#u32,1760985320#u32,1585346786#u32,1053910022#u32,724709799#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_PathModel16.s_29_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [881707106#u32,1071744077#u32,573253446#u32,746861102#u32,1393863025#u32,1619032864#u32,845711239#u32,1311760886#u32,2014776030#u32,1627612094#u32,1839338890#u32,920911638#u32,863752537#u32,26699355#u32,358741485#u32,352718208#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_PathModel16.s_29_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [757594371#u32,1382932400#u32,1457695215#u32,1151149084#u32,724674288#u32,445910383#u32,1604144207#u32,512022794#u32,504482523#u32,368056869#u32,451053264#u32,1383973439#u32,213354562#u32,1814240302#u32,226685125#u32,537691503#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_PathModel16.s_29_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [260401583#u32,908858969#u32,293833352#u32,1983039258#u32,1028353579#u32,218041756#u32,1466417312#u32,83130680#u32,1822663750#u32,1406688212#u32,1842968447#u32,1071788280#u32,1422293462#u32,717876410#u32,1545651243#u32,1764587201#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_PathModel16.s_29_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [127065643#u32,1574438796#u32,1253246531#u32,7802271#u32,302473871#u32,2006764276#u32,346293577#u32,1690976053#u32,2038305951#u32,509403#u32,227143842#u32,1253800239#u32,1994835556#u32,584746648#u32,163695956#u32,510509966#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_PathModel16.s_29_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [51158264#u32,1517078993#u32,301649612#u32,2121332928#u32,214947518#u32,1986097555#u32,286616426#u32,790925239#u32,1000280638#u32,73047365#u32,609700529#u32,875019164#u32,1432444926#u32,507171762#u32,1665059846#u32,1076035360#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_PathModel16.s_29_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [907447114#u32,1607160190#u32,693380421#u32,2132961968#u32,1809661341#u32,1802871019#u32,671872241#u32,1317172612#u32,1424467688#u32,1610337461#u32,1653165263#u32,18370098#u32,828267781#u32,977999562#u32,1801579243#u32,75433971#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_PathModel16.s_29_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [2108238649#u32,1988584907#u32,1768185559#u32,323338001#u32,1973813563#u32,1310073610#u32,406499959#u32,928609652#u32,177178786#u32,310954509#u32,1005540193#u32,463418480#u32,1650245796#u32,1550758258#u32,204603311#u32,514792779#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_PathModel16.s_29_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1729812955#u32,1494679267#u32,894981831#u32,799446364#u32,264217335#u32,1139919297#u32,1776674813#u32,955053619#u32,710142498#u32,1801037372#u32,534585079#u32,1440128139#u32,2057580974#u32,250365775#u32,1650926921#u32,2145048181#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_PathModel16.s_29_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1919539479#u32,1044976366#u32,1340260761#u32,600598908#u32,1664035779#u32,609136675#u32,569316293#u32,544186599#u32,254223669#u32,1054363873#u32,1504571657#u32,1325059781#u32,1801974451#u32,1996872576#u32,2010576497#u32,1000870848#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_PathModel16.s_29_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1221271365#u32,281298876#u32,1842318555#u32,668057428#u32,891221687#u32,1190901464#u32,1596416991#u32,26800423#u32,1486047599#u32,979770035#u32,21147269#u32,208626716#u32,1435645688#u32,283343791#u32,2145578928#u32,1593567844#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_PathModel16.s_29_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1694814022#u32,1847991335#u32,817363271#u32,1888178732#u32,1547820417#u32,629513394#u32,974375254#u32,831418604#u32,687792242#u32,1599804301#u32,198752424#u32,131196268#u32,975629081#u32,1853270684#u32,1539147578#u32,992087833#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_PathModel16.s_29_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1831585957#u32,1647560124#u32,1350360438#u32,261886269#u32,2110199038#u32,724547782#u32,1258985165#u32,2116605939#u32,730098611#u32,1584021330#u32,314903445#u32,611429377#u32,2052965619#u32,1645012249#u32,293794181#u32,1564038371#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_PathModel16.s_29_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [71235157#u32,561336479#u32,2021715933#u32,831357912#u32,593948515#u32,110335229#u32,1732475008#u32,949858646#u32,849182363#u32,972308610#u32,912060318#u32,180196416#u32,425550391#u32,383383629#u32,664136853#u32,513978252#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_PathModel16.s_29_23 := by
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
    exact PV_RunJoin_PathModel16.round_29_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_PathModel16.round_29_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_PathModel16.round_29_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_PathModel16.round_29_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_PathModel16.round_29_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_PathModel16.round_29_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_PathModel16.round_29_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_PathModel16.round_29_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_PathModel16.round_29_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_PathModel16.round_29_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_PathModel16.round_29_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_PathModel16.round_29_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_PathModel16.round_29_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_PathModel16.round_29_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_PathModel16.round_29_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_PathModel16.round_29_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_PathModel16.round_29_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_PathModel16.round_29_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_PathModel16.round_29_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_PathModel16.round_29_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_PathModel16.round_29_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_PathModel16.round_29_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_PathModel16.round_29_23
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
end R1Z.PV_RunJoin_ValidatorCell2919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell3019
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,369#u32,386#u32,403#u32,420#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_30_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [44440674#u32,1095965925#u32,1095966060#u32,1140399220#u32,44441150#u32,1095966401#u32,1095966536#u32,1140399696#u32,88871900#u32,44438551#u32,44438617#u32,133305277#u32,44438431#u32,1095963631#u32,1095963715#u32,1140396960#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_30_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1097105628#u32,1907883600#u32,1404398337#u32,847870613#u32,1106230611#u32,2044509266#u32,242071162#u32,1631927140#u32,1697346441#u32,129356304#u32,620200182#u32,328467573#u32,201942255#u32,1642290840#u32,631270788#u32,1716801117#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_30_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [1127611040#u32,1377984183#u32,1558250836#u32,1364034952#u32,533211840#u32,73528480#u32,945984730#u32,1287521729#u32,1635143550#u32,773868580#u32,1999337811#u32,528582493#u32,1306653029#u32,116668344#u32,1606165707#u32,163281308#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_30_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [1959268546#u32,1301888875#u32,278484041#u32,228808348#u32,1739621844#u32,852964845#u32,381077523#u32,2085543270#u32,1857540573#u32,1919615926#u32,440196932#u32,1725008874#u32,1199403145#u32,2144464276#u32,2017451537#u32,1419284204#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_30_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [365348496#u32,762488752#u32,1836652541#u32,757261658#u32,1628660791#u32,1678687514#u32,1081794141#u32,651104725#u32,344115221#u32,1026327712#u32,910582336#u32,873181805#u32,318246503#u32,709698348#u32,192522950#u32,1468121805#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_30_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [1011647923#u32,312447022#u32,1075779705#u32,431521255#u32,1841826363#u32,639154730#u32,1955116077#u32,418471377#u32,647033618#u32,296847608#u32,2125851183#u32,542359295#u32,1727647035#u32,771227044#u32,982512631#u32,670734209#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_30_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [17027308#u32,1255190607#u32,946819348#u32,521344958#u32,644968960#u32,431801030#u32,1229432286#u32,1955107949#u32,11184456#u32,1773803588#u32,265936919#u32,1948324907#u32,1910020575#u32,932853533#u32,841800369#u32,1337094166#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_30_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1374907189#u32,1826879662#u32,317844104#u32,509585240#u32,1436473441#u32,1038054594#u32,1258816561#u32,1144546265#u32,2003299423#u32,1546358066#u32,160670942#u32,861275875#u32,894387413#u32,802858028#u32,258734732#u32,304736196#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_30_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1249224507#u32,1389408828#u32,198217374#u32,1600870126#u32,316898459#u32,1139017141#u32,1189953472#u32,1946529775#u32,434301317#u32,293203014#u32,880816602#u32,1180364792#u32,1317496545#u32,251122043#u32,1664272633#u32,1303436769#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_30_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [2062393837#u32,1621545360#u32,628571280#u32,193166095#u32,619840557#u32,1276541612#u32,1803425637#u32,255990606#u32,2135613933#u32,130180471#u32,245205240#u32,1020635167#u32,2058506997#u32,37021392#u32,1918042758#u32,1807202997#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_30_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [545734157#u32,366536702#u32,2133902#u32,1665139369#u32,1556232151#u32,1989787958#u32,620036904#u32,96004597#u32,1520635244#u32,2006420860#u32,727054050#u32,263458312#u32,2140198169#u32,1860573063#u32,913672384#u32,1877470684#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_30_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [1359905503#u32,2005085192#u32,1642816294#u32,1856655025#u32,1203503816#u32,1262901113#u32,4892948#u32,1340391757#u32,858847845#u32,2033697017#u32,965070181#u32,579520001#u32,2085454830#u32,1737243517#u32,638220928#u32,1334256602#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_30_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1528265288#u32,919228390#u32,52292139#u32,2045796004#u32,2099722785#u32,1940691830#u32,1218201181#u32,947353413#u32,1472485008#u32,1997020623#u32,1451014569#u32,1806121006#u32,1875182320#u32,1311152035#u32,2089241063#u32,1663156971#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_30_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1215240318#u32,384150159#u32,1716989694#u32,1205654844#u32,1230318520#u32,451219991#u32,1940137562#u32,2113481732#u32,1111925504#u32,1748576918#u32,1392640348#u32,1402882077#u32,7960218#u32,100942268#u32,84891440#u32,587669740#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_30_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [1935492115#u32,1490252663#u32,245114598#u32,1633754586#u32,211232429#u32,1883171419#u32,913478725#u32,1077463591#u32,1698646314#u32,2065194936#u32,1240677248#u32,644850524#u32,1891698950#u32,1381813226#u32,1837485559#u32,1658457846#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_30_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [850308448#u32,1731823797#u32,731800330#u32,334138537#u32,1931430566#u32,307542780#u32,1555602923#u32,479764254#u32,772450979#u32,650497588#u32,1532237709#u32,144431628#u32,797372782#u32,1096859244#u32,1969357507#u32,492624626#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_30_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [514962934#u32,207960305#u32,2087220815#u32,1960174303#u32,1042679154#u32,1249337341#u32,1010789810#u32,1263761353#u32,713097705#u32,1794761864#u32,1971971861#u32,1657565518#u32,56196125#u32,1422315755#u32,646817181#u32,1960693#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_30_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1812100390#u32,356824776#u32,28338807#u32,1547110742#u32,2047846762#u32,810909104#u32,281883686#u32,1572696124#u32,1231057537#u32,46401197#u32,813421955#u32,1341418032#u32,946020013#u32,1025140794#u32,1538139236#u32,1943305746#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_30_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [328069797#u32,1025012943#u32,724865781#u32,414180194#u32,2018576734#u32,757831949#u32,1098531531#u32,389008694#u32,1477246672#u32,1809476364#u32,388615051#u32,1853278213#u32,195652640#u32,1105353876#u32,973478325#u32,635872688#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_30_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [2081483190#u32,1826232589#u32,602660252#u32,1165038760#u32,1694468413#u32,227569317#u32,1674146647#u32,762847683#u32,290715206#u32,664140891#u32,843078412#u32,1226567040#u32,1726241282#u32,587517092#u32,386962486#u32,702922472#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_30_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1273611000#u32,1483319427#u32,1214457299#u32,1122992726#u32,1338415360#u32,1336485862#u32,708080163#u32,1870367921#u32,310941854#u32,349065285#u32,281722642#u32,1917636318#u32,1993364444#u32,71139559#u32,1529321810#u32,1678343901#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_30_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1173103329#u32,372246269#u32,1465730409#u32,1525228319#u32,768153247#u32,373185020#u32,1230934417#u32,1536234187#u32,2128743189#u32,619745168#u32,750428670#u32,408646679#u32,934666341#u32,2126408764#u32,479650056#u32,164094163#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_30_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [2142349696#u32,632952015#u32,243019942#u32,1561436836#u32,1020436789#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_30_23 := by
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
    exact PV_RunJoin_OutputModel16.round_30_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_30_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_30_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_30_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_30_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_30_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_30_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_30_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_30_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_30_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_30_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_30_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_30_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_30_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_30_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_30_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_30_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_30_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_30_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_30_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_30_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_30_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_30_23
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
end R1Z.PV_RunJoin_ValidatorCell3019
