import R1Z.PV_RunJoin_IndexedPair19
import R1Z.PV_RunJoin_OutputCell7017
import R1Z.PV_RunJoin_OutputCell7117
import R1Z.PV_RunJoin_OutputCell7217
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell7019
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,361707637#u32,1111542572#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_70_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [287117213#u32,1517603977#u32,2146791439#u32,1921952141#u32,433441649#u32,2017312924#u32,1619036354#u32,1126323266#u32,233760387#u32,1107820024#u32,127074389#u32,1561527#u32,105264504#u32,608108857#u32,1202951790#u32,1540008334#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_70_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1762508862#u32,1255465431#u32,1628081464#u32,893915396#u32,441529772#u32,1493612380#u32,2144160908#u32,1730117485#u32,978438091#u32,1967208209#u32,733515178#u32,1261305860#u32,1062891939#u32,1507200831#u32,1550711361#u32,1917189154#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_70_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [907891647#u32,1371824039#u32,1539198311#u32,541678212#u32,478018438#u32,1258065707#u32,2119149802#u32,661476327#u32,1994407808#u32,2140210437#u32,28105879#u32,190436848#u32,1483849603#u32,565641960#u32,1033332860#u32,1234397099#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_70_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [309247647#u32,1966743482#u32,78069815#u32,2116708605#u32,1776810158#u32,1085445172#u32,1802732200#u32,432351236#u32,1215289365#u32,229837707#u32,1983983697#u32,315768786#u32,1144493045#u32,483881700#u32,644243461#u32,1352339533#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_70_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [247952246#u32,73088116#u32,604346656#u32,258175612#u32,2091728817#u32,96963357#u32,1938049228#u32,1872184902#u32,223204097#u32,1762689175#u32,1900378381#u32,756377191#u32,1066920528#u32,330658904#u32,462440304#u32,1651833988#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_70_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [1315044475#u32,1018834742#u32,6956291#u32,1978449074#u32,499707986#u32,349676691#u32,686296159#u32,506496122#u32,1598583631#u32,1222609556#u32,1313024588#u32,247818341#u32,900268712#u32,359988381#u32,1545014866#u32,887338924#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_70_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [317280624#u32,1173878482#u32,168956322#u32,1626389095#u32,2005223981#u32,1454903502#u32,641684358#u32,358540843#u32,762802043#u32,1757961261#u32,367458830#u32,1606687092#u32,697488646#u32,1214583382#u32,275194803#u32,1089089891#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_70_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1880502658#u32,1777773475#u32,941807637#u32,667000432#u32,1613301312#u32,260030908#u32,1810441626#u32,2075672475#u32,1605792382#u32,1817895586#u32,1072098688#u32,1704329417#u32,2124382005#u32,1754552579#u32,903365944#u32,1432499877#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_70_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1383792480#u32,566196741#u32,672038540#u32,1456424994#u32,957415527#u32,801434147#u32,887980476#u32,634959199#u32,318901697#u32,313225530#u32,1400819808#u32,399862548#u32,665816585#u32,1309262507#u32,1516569657#u32,1852733733#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_70_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1667621125#u32,636055230#u32,1413935569#u32,1600591171#u32,1286731764#u32,7902959#u32,567946310#u32,2052541579#u32,87086412#u32,798699230#u32,2137749332#u32,1524316083#u32,1978343076#u32,1960106941#u32,105303838#u32,2102382997#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_70_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [1492314830#u32,1303387030#u32,1347719291#u32,627245543#u32,223767677#u32,793779144#u32,1661744544#u32,1033490389#u32,1076974301#u32,1123388215#u32,1436811475#u32,1531045939#u32,194726483#u32,1588995906#u32,257274655#u32,2036115319#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_70_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [410018722#u32,1154045425#u32,398613330#u32,212156920#u32,1640799811#u32,1813706464#u32,1486876275#u32,1569533881#u32,264415515#u32,1822716384#u32,119310600#u32,362575299#u32,1617141057#u32,15329718#u32,1353238960#u32,512830740#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_70_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1119071391#u32,804267381#u32,447448616#u32,498849636#u32,2039202209#u32,752237969#u32,2133106169#u32,1316142578#u32,1283153171#u32,261664861#u32,1565192124#u32,847446583#u32,1590626204#u32,1704218616#u32,1342119980#u32,406523046#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_70_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [3610785#u32,425316530#u32,515946381#u32,1616447693#u32,902281292#u32,919438418#u32,1308453500#u32,102311908#u32,655897865#u32,35260508#u32,354983463#u32,428679565#u32,1247625968#u32,2103959046#u32,2038430523#u32,1980750770#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_70_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [754471180#u32,1025124799#u32,1631701031#u32,623148100#u32,1375607664#u32,278437428#u32,1668130976#u32,705319440#u32,802872756#u32,1036563729#u32,1178138038#u32,1977166910#u32,1277062052#u32,457316289#u32,559829645#u32,2138260780#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_70_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [1026129441#u32,1256099927#u32,1346893543#u32,576083881#u32,498418205#u32,391006682#u32,2071558832#u32,274262701#u32,2066956487#u32,1450801171#u32,1906000073#u32,545805651#u32,1530460575#u32,330609721#u32,923469814#u32,1391551870#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_70_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [566412222#u32,1597391266#u32,887594778#u32,498143216#u32,33669685#u32,154947310#u32,59180906#u32,714235027#u32,771233094#u32,231720184#u32,22730968#u32,430761308#u32,864790553#u32,1097202469#u32,408086614#u32,2044090157#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_70_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [921222739#u32,980370774#u32,1158169064#u32,1375552372#u32,1799820635#u32,1862136468#u32,1276768500#u32,2144348296#u32,1464051425#u32,721288143#u32,1184654270#u32,697222889#u32,1346121878#u32,1510106214#u32,1331960838#u32,845608800#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_70_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [349428157#u32,1372598103#u32,561081810#u32,1599469523#u32,1905890527#u32,121639759#u32,446630036#u32,191564865#u32,959732440#u32,358398295#u32,149939254#u32,63930163#u32,494124560#u32,813340418#u32,627325285#u32,247549647#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_70_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1287523894#u32,785424106#u32,1103742657#u32,1579931793#u32,982172183#u32,780028606#u32,1423537984#u32,1887171966#u32,1340045203#u32,306877116#u32,392108517#u32,843127872#u32,1523662859#u32,1982879957#u32,403994089#u32,2102420001#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_70_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1427358298#u32,128723350#u32,1460800710#u32,142657035#u32,743373017#u32,275650141#u32,2111939415#u32,1653054652#u32,1796407483#u32,2121323632#u32,353032391#u32,1320529774#u32,834508404#u32,1518733024#u32,2006190355#u32,562939735#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_70_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [359765086#u32,1395679046#u32,1640992123#u32,1714816794#u32,228532847#u32,989170106#u32,898441725#u32,908673140#u32,653153538#u32,1307970129#u32,1832718761#u32,1622333775#u32,285307937#u32,1661124646#u32,501101487#u32,2033586400#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_70_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,352883826#u32,459345458#u32,1455730454#u32,1954324198#u32,2107137027#u32,2040782725#u32,1631610898#u32,1814297336#u32,1077073819#u32,1365220188#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_70_23 := by
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
    exact PV_RunJoin_OutputModel16.round_70_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_70_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_70_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_70_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_70_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_70_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_70_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_70_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_70_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_70_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_70_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_70_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_70_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_70_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_70_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_70_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_70_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_70_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_70_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_70_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_70_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_70_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_70_23
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
end R1Z.PV_RunJoin_ValidatorCell7019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell7119
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,352883826#u32,459345458#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_71_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [1711954657#u32,612359055#u32,998094614#u32,1644174737#u32,1173479589#u32,949673321#u32,1745332263#u32,753048679#u32,2059038370#u32,1133806497#u32,1293419552#u32,533447620#u32,2117293196#u32,1917010865#u32,661775818#u32,785250098#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_71_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1262724429#u32,364316315#u32,1052646691#u32,2018469122#u32,164721006#u32,1221599867#u32,1537570876#u32,1494487913#u32,2044751959#u32,2095165382#u32,176564083#u32,156846231#u32,845677413#u32,1761619207#u32,301299151#u32,1910821773#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_71_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [86864662#u32,1030956474#u32,596574380#u32,1416700350#u32,1092043436#u32,620178406#u32,904564508#u32,2060110991#u32,1645147694#u32,2128089746#u32,226743932#u32,1558906522#u32,1739571701#u32,339097735#u32,1812107270#u32,508386258#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_71_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [1641558695#u32,847339416#u32,175226#u32,972265605#u32,1010932578#u32,1080665646#u32,1812028547#u32,1888714873#u32,89346979#u32,1096658981#u32,834507963#u32,2066892552#u32,603916456#u32,1191625953#u32,974992148#u32,1539239686#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_71_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [1493732404#u32,1491755108#u32,187899859#u32,845157597#u32,1616276404#u32,512878817#u32,1220627435#u32,2109904958#u32,1371272981#u32,1424828397#u32,1394065791#u32,1411267031#u32,403446225#u32,479339509#u32,1020702290#u32,910226166#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_71_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [846558133#u32,1232239406#u32,116284016#u32,973631039#u32,1933277295#u32,1504094429#u32,145856572#u32,1630415496#u32,1317250459#u32,1571817587#u32,1334712674#u32,1411749197#u32,1942110412#u32,2038786322#u32,1202804640#u32,1669236555#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_71_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [156837775#u32,321744536#u32,1469556809#u32,836545639#u32,1670821608#u32,1680179524#u32,1609431787#u32,356881818#u32,193839416#u32,2042849060#u32,35683814#u32,588238318#u32,299143258#u32,603959340#u32,1972058906#u32,1359395430#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_71_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [581011087#u32,1904104564#u32,226506352#u32,633575290#u32,2064031010#u32,547945001#u32,1544569684#u32,800476263#u32,624001512#u32,565709520#u32,1615363565#u32,1529858622#u32,1885088337#u32,1247541212#u32,2078169959#u32,414681066#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_71_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1490665393#u32,1416944733#u32,2113336520#u32,2047141329#u32,992702720#u32,1837509244#u32,1694429823#u32,1351197120#u32,2075622413#u32,453072940#u32,82722539#u32,1603957582#u32,1749074943#u32,1626189078#u32,279610311#u32,1793112407#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_71_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1282834770#u32,1565168074#u32,79929087#u32,1894337716#u32,1647394160#u32,1631083834#u32,682886502#u32,725493141#u32,1687403624#u32,170779043#u32,1104241044#u32,806003040#u32,559263613#u32,1947952611#u32,1253656087#u32,1110281006#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_71_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [413859977#u32,523314909#u32,1265488656#u32,93046758#u32,1399881880#u32,1433168062#u32,1483162076#u32,292551272#u32,197446007#u32,1875392550#u32,124577569#u32,1811716883#u32,2010529127#u32,459247392#u32,1693605835#u32,1293228397#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_71_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [1426909523#u32,944349074#u32,804527830#u32,793221197#u32,882670970#u32,1876886687#u32,637580363#u32,1964446397#u32,2071802944#u32,1632673684#u32,1286929648#u32,1657386548#u32,1623553706#u32,2095089252#u32,1224629671#u32,847647455#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_71_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1470464396#u32,1505969884#u32,23192823#u32,1587021951#u32,1180537629#u32,527036744#u32,1636839603#u32,1732138692#u32,1611909061#u32,1914256396#u32,1970104751#u32,1021113251#u32,1347354491#u32,1125311930#u32,1347252296#u32,878251094#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_71_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1684396871#u32,2130932206#u32,671347968#u32,530599185#u32,1479328766#u32,467615638#u32,1464222090#u32,1960172613#u32,790892018#u32,1048328182#u32,1525082813#u32,1954177709#u32,87007014#u32,1588513947#u32,1566866271#u32,831951812#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_71_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [2020786730#u32,1944483588#u32,1156247318#u32,1935948122#u32,910763275#u32,852950649#u32,1571501675#u32,710547088#u32,115998277#u32,1897593746#u32,277740525#u32,453895077#u32,1757922913#u32,671741037#u32,848487034#u32,145188931#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_71_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [49175000#u32,185072393#u32,553083441#u32,1689413999#u32,1231727711#u32,1150380954#u32,1284002171#u32,765929497#u32,203466379#u32,840767206#u32,1326528648#u32,1968953189#u32,267238966#u32,339531785#u32,140424855#u32,2137298258#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_71_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [141318561#u32,294105325#u32,1215199814#u32,424237987#u32,1372920032#u32,1335259020#u32,394913111#u32,1883880506#u32,382925680#u32,597072968#u32,1264703580#u32,1140200591#u32,1044806111#u32,1015152642#u32,1640709698#u32,466793645#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_71_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [53631865#u32,1268947469#u32,1257758125#u32,524310445#u32,1220784165#u32,864149994#u32,727159814#u32,1284110296#u32,597205303#u32,1354183015#u32,1098668923#u32,459530655#u32,156686514#u32,974882657#u32,1497123563#u32,1858609349#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_71_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [2103809354#u32,1536071278#u32,635156412#u32,216881942#u32,1443462541#u32,1208621831#u32,2061401387#u32,845804167#u32,1547474948#u32,1193108482#u32,22669933#u32,1309011917#u32,1795309238#u32,1908693358#u32,895604125#u32,816962033#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_71_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1252332223#u32,2004303008#u32,1548976804#u32,1773001953#u32,1877949705#u32,517705094#u32,1423656455#u32,1373383596#u32,734483363#u32,1208160457#u32,1719908130#u32,2087220587#u32,769355796#u32,1414151951#u32,1606002375#u32,2059752988#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_71_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1543939791#u32,916095341#u32,1571975635#u32,477644739#u32,954714890#u32,1487902484#u32,1343178985#u32,433799040#u32,380945547#u32,1227297437#u32,10227971#u32,1229418267#u32,1938065678#u32,1154171660#u32,346504470#u32,148435603#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_71_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1081422286#u32,459441233#u32,375365063#u32,859114407#u32,1976577755#u32,321802380#u32,1824261653#u32,515156372#u32,1830021745#u32,1319203380#u32,845851379#u32,183946798#u32,1428154998#u32,2110477431#u32,2007616873#u32,2066967997#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_71_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,514446081#u32,115798455#u32,1675315503#u32,623996#u32,1826822856#u32,2018969870#u32,1059096109#u32,1893786108#u32,895341560#u32,696077111#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_71_23 := by
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
    exact PV_RunJoin_OutputModel16.round_71_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_71_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_71_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_71_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_71_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_71_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_71_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_71_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_71_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_71_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_71_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_71_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_71_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_71_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_71_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_71_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_71_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_71_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_71_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_71_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_71_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_71_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_71_23
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
end R1Z.PV_RunJoin_ValidatorCell7119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell7219
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,514446081#u32,115798455#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_72_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [213544154#u32,486457673#u32,86492999#u32,1698363251#u32,730766096#u32,59994348#u32,143583562#u32,157432886#u32,2123995113#u32,2009169964#u32,445678441#u32,1145870422#u32,1926954472#u32,2124862487#u32,9566515#u32,799613535#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_72_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1715932507#u32,1975440476#u32,1845249461#u32,1111821657#u32,93049171#u32,2027389984#u32,941534293#u32,2020957512#u32,668198226#u32,372878269#u32,573898391#u32,2007049904#u32,872810959#u32,1424095867#u32,911425749#u32,1641220279#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_72_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [711460361#u32,1060107143#u32,1268048439#u32,148909318#u32,612933141#u32,1175192165#u32,1318313627#u32,24670795#u32,137502025#u32,1580577756#u32,1762628355#u32,144251518#u32,335944539#u32,1745404475#u32,1641792609#u32,1446711270#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_72_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [265656357#u32,104170449#u32,632002172#u32,2026007599#u32,1991133573#u32,1421934789#u32,193374953#u32,11397766#u32,154523756#u32,1034179694#u32,1182119698#u32,374637888#u32,2122854050#u32,1952912962#u32,67028276#u32,383809261#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_72_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [503522354#u32,2132293118#u32,1200653575#u32,92930483#u32,2128453429#u32,1660867805#u32,1685689227#u32,32821590#u32,1605617796#u32,562569541#u32,929649587#u32,359005582#u32,670225381#u32,1522346467#u32,1842032081#u32,2059443867#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_72_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [627795163#u32,1966475014#u32,88005399#u32,205903828#u32,1829423799#u32,638263012#u32,89145985#u32,1934763656#u32,1342313319#u32,2118063690#u32,460103363#u32,1442231220#u32,1352301316#u32,1083620966#u32,218545875#u32,347719305#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_72_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [422159919#u32,1713303531#u32,2070322962#u32,570443829#u32,1497317027#u32,1369102121#u32,452016390#u32,1165134622#u32,1911725236#u32,805254113#u32,593753536#u32,1545876387#u32,1078557963#u32,545425712#u32,1347581419#u32,930222680#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_72_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1410041675#u32,1135598560#u32,1415457306#u32,1704070345#u32,663413010#u32,2000576142#u32,1001917627#u32,976466839#u32,1457473126#u32,1556401492#u32,1835527439#u32,550184825#u32,221404167#u32,2145188917#u32,411483207#u32,1877564120#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_72_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1298378783#u32,1235452022#u32,783284427#u32,473683901#u32,1112190248#u32,2044300676#u32,2096446468#u32,316705395#u32,1972819948#u32,1254160719#u32,631759873#u32,946550959#u32,1366591458#u32,1157702788#u32,1679244572#u32,1624015976#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_72_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1715346110#u32,402702773#u32,733819605#u32,1061986355#u32,1622321794#u32,1811290509#u32,1829028317#u32,109043208#u32,432617396#u32,257331412#u32,1844266603#u32,31995980#u32,1599706523#u32,394159039#u32,1827382613#u32,1388708567#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_72_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [61521042#u32,969132061#u32,2034068498#u32,519407414#u32,660101758#u32,1629790021#u32,1113276963#u32,1102743659#u32,106881154#u32,2018761350#u32,1457305047#u32,625460901#u32,1417051710#u32,984797735#u32,1953362771#u32,614116340#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_72_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [89150856#u32,932757617#u32,1884278905#u32,2041255212#u32,949472326#u32,270462128#u32,1228750020#u32,1819743028#u32,759511386#u32,1370455876#u32,1890342666#u32,2050968828#u32,1302121841#u32,845075885#u32,2004806849#u32,701055369#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_72_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [2011003177#u32,369164666#u32,1057481212#u32,1158976956#u32,589734716#u32,1616317450#u32,101702043#u32,2083327550#u32,17100342#u32,233276844#u32,264531086#u32,1396183120#u32,2014737519#u32,332634680#u32,1422473351#u32,535925915#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_72_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [956086460#u32,30409342#u32,1776207100#u32,2185206#u32,84155110#u32,1900003759#u32,768226405#u32,1997705409#u32,1850088452#u32,1398058271#u32,2105620865#u32,1825835882#u32,979173129#u32,1381829357#u32,135452109#u32,6963431#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_72_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [356967152#u32,2092498786#u32,1319536350#u32,2070830268#u32,587846677#u32,249894883#u32,875530640#u32,1066216800#u32,502726483#u32,1335237771#u32,2144273616#u32,1000319615#u32,449457020#u32,1034184211#u32,1708098807#u32,1003486649#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_72_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [637665173#u32,1975372413#u32,374462680#u32,1723743758#u32,290679749#u32,1733708108#u32,2130050343#u32,1548755770#u32,1954837688#u32,253843130#u32,890769177#u32,1940701838#u32,1047810509#u32,311011821#u32,998289642#u32,1992180410#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_72_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [57365153#u32,1595735686#u32,369288633#u32,72887364#u32,1945801265#u32,1589889237#u32,1209981192#u32,2103968438#u32,731484285#u32,179695143#u32,1234934193#u32,898114174#u32,1939399589#u32,1406827853#u32,1104441225#u32,739910021#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_72_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [958935551#u32,521778379#u32,1812103606#u32,1365075796#u32,1607550931#u32,741950368#u32,1138218838#u32,436036611#u32,214234352#u32,1978326361#u32,778271889#u32,1109695733#u32,1550938922#u32,1599086641#u32,2009167896#u32,1635913336#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_72_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1823499874#u32,1335239471#u32,142701010#u32,1978796982#u32,788966658#u32,1947248745#u32,729241909#u32,802516785#u32,318170737#u32,458868816#u32,1047442391#u32,2051786408#u32,1591854464#u32,948493836#u32,1820911141#u32,1056256360#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_72_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [197763048#u32,946472180#u32,1894478953#u32,100941530#u32,536928716#u32,1255313069#u32,2126968711#u32,46170584#u32,1552540284#u32,899253043#u32,1394497893#u32,2121332220#u32,1342774959#u32,1035740073#u32,184938664#u32,2067463388#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_72_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [638066133#u32,781397022#u32,1981048872#u32,1648627123#u32,1432209370#u32,460479953#u32,336292449#u32,895051209#u32,172226943#u32,1948332943#u32,495478418#u32,3112736#u32,86667386#u32,116909715#u32,1006932203#u32,668382407#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_72_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [893688601#u32,1780819041#u32,936891468#u32,53712234#u32,569129250#u32,1144021791#u32,1667666831#u32,727388145#u32,1435236442#u32,187187370#u32,1487373853#u32,1214900179#u32,1244739800#u32,756880034#u32,1348125398#u32,980424727#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_72_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,351180429#u32,2094192877#u32,1421708941#u32,1301484970#u32,2114944774#u32,1692228352#u32,498921295#u32,940488105#u32,485657316#u32,1184992977#u32,1828563447#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_72_23 := by
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
    exact PV_RunJoin_OutputModel16.round_72_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_72_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_72_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_72_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_72_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_72_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_72_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_72_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_72_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_72_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_72_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_72_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_72_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_72_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_72_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_72_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_72_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_72_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_72_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_72_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_72_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_72_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_72_23
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
end R1Z.PV_RunJoin_ValidatorCell7219
