import R1Z.PV_RunJoin_IndexedPair19
import R1Z.PV_RunJoin_OutputCell5517
import R1Z.PV_RunJoin_OutputCell5617
import R1Z.PV_RunJoin_OutputCell5717
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell5519
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,707737539#u32,1640113194#u32,1531834504#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_55_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [210320689#u32,1352384607#u32,1584159144#u32,246637079#u32,737574218#u32,407151300#u32,1190645720#u32,682437263#u32,895296005#u32,1636788007#u32,247780149#u32,1658596765#u32,385210135#u32,1874123590#u32,438759569#u32,553995566#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_55_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [870585433#u32,1800414885#u32,290256921#u32,1641300425#u32,1399847096#u32,862214521#u32,2010170964#u32,1489608772#u32,1996350231#u32,940477677#u32,120068175#u32,888769136#u32,636335179#u32,351589003#u32,84463619#u32,1887875909#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_55_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [730743620#u32,1992956738#u32,142751938#u32,986619621#u32,1276962979#u32,474755728#u32,904972683#u32,476005803#u32,1271875474#u32,778924627#u32,1496327527#u32,927239565#u32,1502417828#u32,405308773#u32,777625811#u32,1301408899#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_55_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [1142586902#u32,588564839#u32,588264325#u32,966171816#u32,1589990703#u32,1500124031#u32,753541020#u32,1104258095#u32,1744679627#u32,694342634#u32,97366531#u32,563010251#u32,1401877359#u32,667841377#u32,972933030#u32,1132121422#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_55_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [231664975#u32,54700572#u32,915764206#u32,273142843#u32,1765145675#u32,1708686180#u32,1935080571#u32,618587418#u32,171493148#u32,383333382#u32,1971478888#u32,156145486#u32,1897418258#u32,46928139#u32,436194009#u32,1136787039#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_55_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [631360443#u32,595307993#u32,224652186#u32,1633178793#u32,1776870939#u32,2109782537#u32,186159930#u32,1475496527#u32,1016893895#u32,2037189098#u32,700360553#u32,162391271#u32,704339971#u32,612091171#u32,94739901#u32,513313601#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_55_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [204251279#u32,159306035#u32,13302414#u32,1801745920#u32,894063672#u32,1108263929#u32,1226148508#u32,1653978949#u32,877397782#u32,1393364556#u32,1621149863#u32,1146197135#u32,1375964632#u32,1464595863#u32,887204095#u32,1900306570#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_55_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [928239458#u32,2064791718#u32,1932090511#u32,522534775#u32,468060471#u32,310355724#u32,340048646#u32,385956069#u32,395768488#u32,2124526617#u32,1958086264#u32,182214654#u32,1666087924#u32,1861833497#u32,1175657557#u32,1377716732#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_55_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1600431117#u32,1783565190#u32,1435470847#u32,1808912572#u32,1315773593#u32,389497762#u32,2010395556#u32,797641771#u32,985016055#u32,284224733#u32,1196865157#u32,893170747#u32,1052470195#u32,1141066332#u32,2103941362#u32,960067356#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_55_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [267409257#u32,1325092390#u32,264985247#u32,334726547#u32,1477781356#u32,1478524098#u32,1597159229#u32,1198476663#u32,1069530714#u32,1436098497#u32,1065769178#u32,804256071#u32,1378005582#u32,927163553#u32,824557575#u32,1539880210#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_55_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [1909218318#u32,647633187#u32,1999994938#u32,661446985#u32,407373410#u32,1504089895#u32,1039512244#u32,863119584#u32,931002428#u32,1891536039#u32,1895970040#u32,1462976762#u32,770219909#u32,818357918#u32,933395490#u32,212959886#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_55_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [1337967848#u32,1324071711#u32,381461106#u32,1174742817#u32,1787942157#u32,1119556727#u32,1728575627#u32,81517078#u32,1733148723#u32,1725843933#u32,824542596#u32,1549880546#u32,1010978166#u32,1912158815#u32,1717754270#u32,719305567#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_55_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1628796890#u32,771012500#u32,209863001#u32,1998428410#u32,865576163#u32,179979245#u32,1074269678#u32,369066487#u32,99161692#u32,1028840002#u32,1964969469#u32,1943480320#u32,683133829#u32,765523313#u32,1272472279#u32,443044404#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_55_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1300110134#u32,1038740186#u32,687453688#u32,1818990385#u32,749886049#u32,999911959#u32,284619030#u32,265662737#u32,75522380#u32,1657763264#u32,204286703#u32,41238977#u32,157670772#u32,1297189398#u32,1096875806#u32,1646880790#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_55_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [267251513#u32,1194552804#u32,1530719994#u32,989323217#u32,1859933716#u32,1122018433#u32,673686990#u32,2125842257#u32,1232742670#u32,1488929743#u32,1039482731#u32,1566937944#u32,1157104995#u32,1808738738#u32,148423787#u32,1902135132#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_55_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [980441236#u32,1240552224#u32,959955761#u32,1855808641#u32,2040567266#u32,818425172#u32,129146630#u32,808434107#u32,1070754949#u32,1107408109#u32,1471910699#u32,1542680808#u32,57300602#u32,1294637859#u32,1693675028#u32,1243269116#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_55_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [1729683139#u32,1967668322#u32,499543973#u32,1707899721#u32,2019268697#u32,937016968#u32,564840964#u32,927291418#u32,344796162#u32,755750598#u32,430151680#u32,1650816192#u32,1982212636#u32,1377816535#u32,1650544181#u32,1934851447#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_55_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [739389064#u32,74512600#u32,1253415871#u32,643475868#u32,1376091972#u32,214213884#u32,1149369597#u32,1618920208#u32,1438563721#u32,452952783#u32,495500610#u32,1718929601#u32,1416387070#u32,52340101#u32,910401238#u32,211854108#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_55_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [555561633#u32,1950489314#u32,87841162#u32,154912892#u32,2147294255#u32,1008431564#u32,1098172#u32,260171323#u32,1328539360#u32,1867772224#u32,314977015#u32,1012743897#u32,2064709413#u32,422732698#u32,1060919374#u32,317537100#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_55_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [452496391#u32,1760616570#u32,334130525#u32,90585324#u32,509101788#u32,1608598344#u32,1741479137#u32,1701436424#u32,226570543#u32,1113234795#u32,921238339#u32,1054725811#u32,1596061377#u32,1224863998#u32,875022868#u32,2127347314#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_55_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1932788401#u32,594275382#u32,1068039414#u32,1425021855#u32,804726345#u32,900664947#u32,633670076#u32,766826248#u32,1134194384#u32,1908336371#u32,1338369552#u32,502944546#u32,1349998038#u32,1671684373#u32,878124383#u32,1110931020#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_55_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [581155984#u32,1494323402#u32,1394627590#u32,241021780#u32,739970961#u32,943308971#u32,648584917#u32,2074209140#u32,739041611#u32,369743955#u32,299701003#u32,1649469353#u32,304288113#u32,1776239459#u32,1603196367#u32,415365919#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_55_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,1644297524#u32,121114825#u32,74900099#u32,272182702#u32,1433516637#u32,608854492#u32,1537979930#u32,595455334#u32,690270964#u32,837783390#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_55_23 := by
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
    exact PV_RunJoin_OutputModel16.round_55_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_55_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_55_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_55_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_55_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_55_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_55_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_55_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_55_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_55_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_55_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_55_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_55_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_55_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_55_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_55_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_55_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_55_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_55_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_55_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_55_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_55_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_55_23
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
end R1Z.PV_RunJoin_ValidatorCell5519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell5619
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,1644297524#u32,121114825#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_56_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [1154952564#u32,1822239224#u32,678627901#u32,799818050#u32,322422830#u32,1378498898#u32,1203747828#u32,1258290114#u32,1745350976#u32,100546822#u32,1911556984#u32,1099905972#u32,1862813369#u32,898433013#u32,1605623105#u32,241629126#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_56_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [174476549#u32,1386816038#u32,1498201176#u32,1795280802#u32,1534286355#u32,948175559#u32,1709992533#u32,6991511#u32,261108728#u32,611134499#u32,597785403#u32,1309496274#u32,2016255940#u32,726681289#u32,1502747545#u32,1450211798#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_56_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [1428764243#u32,1884517166#u32,860054447#u32,848171598#u32,1492234493#u32,2418029#u32,112368097#u32,1141788106#u32,1969906161#u32,1557313765#u32,412340557#u32,821447567#u32,1173418783#u32,1317722160#u32,280769864#u32,2135230136#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_56_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [1021952441#u32,1483078510#u32,5621833#u32,1396825581#u32,1330821836#u32,1884062248#u32,2003595833#u32,963415308#u32,2030973199#u32,645668466#u32,1579566162#u32,370986240#u32,534118744#u32,3592539#u32,1812975952#u32,1142305018#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_56_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [290423274#u32,310794322#u32,556309218#u32,1774495165#u32,40871663#u32,1317138994#u32,2093006884#u32,211291439#u32,1001214989#u32,203148014#u32,75376078#u32,793918840#u32,1134836308#u32,987161744#u32,1758161103#u32,2055172669#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_56_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [2123994008#u32,1042791410#u32,1844615524#u32,1387526807#u32,1058970392#u32,331384522#u32,1136224319#u32,1369747302#u32,38496860#u32,1198281144#u32,607689668#u32,1333324170#u32,854324361#u32,1690665227#u32,1611222123#u32,501176479#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_56_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [1692433846#u32,1298467122#u32,1797423113#u32,1510815646#u32,137504260#u32,1262860770#u32,107631921#u32,2020157160#u32,888306498#u32,2072970702#u32,1907121761#u32,500561711#u32,231635451#u32,1870675874#u32,896740681#u32,1742506238#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_56_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [2064556409#u32,1364930177#u32,1513825634#u32,1814758345#u32,1166497135#u32,944882552#u32,1363200880#u32,507502475#u32,2100545155#u32,318501958#u32,896511196#u32,1667832073#u32,1396017346#u32,333372687#u32,446356162#u32,217380104#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_56_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1019735256#u32,237167974#u32,1899889065#u32,1836303883#u32,1761763936#u32,1105456747#u32,1692476664#u32,1287625139#u32,1454045409#u32,951844106#u32,2071668879#u32,1314411345#u32,1843399601#u32,1946910931#u32,707318143#u32,835702990#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_56_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [717584912#u32,609363393#u32,2024489902#u32,1274960010#u32,1581405025#u32,879634195#u32,844357492#u32,1175825729#u32,1806414129#u32,1378634444#u32,47284279#u32,459561510#u32,396721107#u32,1986280032#u32,2129586819#u32,1727898618#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_56_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [53667439#u32,693307323#u32,1985440087#u32,888816676#u32,1997765895#u32,1273189168#u32,1333579910#u32,174862941#u32,1524202213#u32,827043486#u32,1258405392#u32,1252214118#u32,880494563#u32,328801580#u32,2051203304#u32,687583221#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_56_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [1325250506#u32,1469621866#u32,452227423#u32,36613953#u32,1726056174#u32,1819988408#u32,501198723#u32,1230124532#u32,453185930#u32,2046049553#u32,893247751#u32,1654392835#u32,390204366#u32,1972414587#u32,515512562#u32,1580920998#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_56_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [581208493#u32,12194343#u32,1594510970#u32,836511936#u32,1613603634#u32,1892583241#u32,1696029731#u32,2108614880#u32,715796695#u32,492731824#u32,547719526#u32,1772201999#u32,1788555660#u32,1396729476#u32,899320438#u32,432547890#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_56_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [2114783023#u32,1284461101#u32,166321404#u32,323347208#u32,1296193948#u32,1488827556#u32,1858126975#u32,932149317#u32,552446897#u32,710078529#u32,1643829515#u32,1716927802#u32,839309997#u32,1702259110#u32,286291361#u32,1946645398#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_56_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [941840289#u32,1624798343#u32,672980050#u32,1633726074#u32,2119954238#u32,539258021#u32,1818341973#u32,2015835061#u32,186579707#u32,1731814318#u32,2142065001#u32,2015153956#u32,1872678619#u32,783471893#u32,1327084394#u32,132123241#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_56_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [1736392455#u32,317946373#u32,39108130#u32,933085032#u32,620396405#u32,878825425#u32,1045516344#u32,1005056761#u32,1100514056#u32,1803465803#u32,1734389114#u32,2131580032#u32,200704357#u32,1734368470#u32,198202519#u32,1015289149#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_56_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [1524311333#u32,393243569#u32,153513456#u32,1660153677#u32,743501142#u32,1251602114#u32,1319565499#u32,2121904137#u32,1354659309#u32,53558659#u32,120773863#u32,1506083213#u32,1420399785#u32,464692572#u32,784891260#u32,431647412#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_56_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1800283021#u32,383536118#u32,297319461#u32,188456316#u32,1643334391#u32,688573550#u32,1414199224#u32,500687556#u32,1587992341#u32,816407371#u32,1256160382#u32,1334098813#u32,838931823#u32,683863582#u32,1042943757#u32,1780487097#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_56_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1749181137#u32,1778534781#u32,1989637585#u32,1340280#u32,1656771909#u32,1674757228#u32,1552217244#u32,1226747542#u32,647071846#u32,2089371880#u32,1360525278#u32,517855096#u32,1976822279#u32,246256105#u32,1521269681#u32,1725944263#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_56_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [646498947#u32,1526264851#u32,451173245#u32,1324823896#u32,1059728337#u32,1745001687#u32,1134605617#u32,781092945#u32,1390406484#u32,1019923229#u32,1866690929#u32,339777371#u32,851933799#u32,930115243#u32,1584856385#u32,1502702707#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_56_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1767845462#u32,13475269#u32,1800636359#u32,1603461266#u32,104914133#u32,2009496616#u32,1356795827#u32,147641717#u32,950312779#u32,280069760#u32,1648893378#u32,992384169#u32,1402674343#u32,978844252#u32,839579241#u32,1150090217#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_56_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1588187675#u32,469281555#u32,146200516#u32,585094780#u32,1762635649#u32,2008387219#u32,1521112366#u32,673849039#u32,997848400#u32,1990971323#u32,1954087279#u32,1071782328#u32,1815773507#u32,1226549839#u32,1560828850#u32,1692784096#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_56_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,358772057#u32,1351134296#u32,368405069#u32,1782505896#u32,1202988806#u32,1220246091#u32,2063970251#u32,468240264#u32,990891850#u32,1774689476#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_56_23 := by
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
    exact PV_RunJoin_OutputModel16.round_56_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_56_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_56_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_56_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_56_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_56_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_56_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_56_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_56_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_56_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_56_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_56_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_56_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_56_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_56_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_56_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_56_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_56_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_56_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_56_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_56_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_56_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_56_23
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
end R1Z.PV_RunJoin_ValidatorCell5619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell5719
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,358772057#u32,1351134296#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_57_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [1822620517#u32,1340651037#u32,248509382#u32,1594875044#u32,1149741265#u32,738091654#u32,1599510873#u32,1664667090#u32,1602811428#u32,718408916#u32,2052584187#u32,120309561#u32,444305197#u32,1618667706#u32,969709146#u32,978531862#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_57_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1092704588#u32,461635563#u32,1456161716#u32,1388924713#u32,1350212425#u32,640806972#u32,1443015599#u32,480156224#u32,140516141#u32,131471094#u32,1168060872#u32,1795841954#u32,601529274#u32,932674382#u32,721359757#u32,603949151#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_57_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [1626943377#u32,1050096733#u32,896489540#u32,25903683#u32,1466960682#u32,775548401#u32,1927429162#u32,2128298387#u32,291187300#u32,210390743#u32,91248949#u32,1840096112#u32,888936798#u32,951872547#u32,603966563#u32,109027881#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_57_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [882729492#u32,159321868#u32,1482663817#u32,743851567#u32,317109853#u32,1189610790#u32,1198767985#u32,976814022#u32,834450264#u32,1393144040#u32,160233964#u32,1612747330#u32,1369565289#u32,66006751#u32,633052100#u32,772740055#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_57_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [225835164#u32,627470120#u32,125834286#u32,1232857730#u32,1055401899#u32,107403031#u32,1336078142#u32,1182030706#u32,621273621#u32,695206183#u32,966522963#u32,1891997194#u32,114840063#u32,1647238068#u32,1626424566#u32,2024988823#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_57_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [439935232#u32,633898620#u32,258097072#u32,642892126#u32,2007192751#u32,1724876996#u32,1958739751#u32,494466039#u32,72557049#u32,1885552294#u32,1883464992#u32,1505936748#u32,178387210#u32,927942763#u32,584939589#u32,1626998969#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_57_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [1161385050#u32,32144803#u32,2061923974#u32,1969814687#u32,423402662#u32,1226474355#u32,1948376099#u32,979301621#u32,95613867#u32,1063296519#u32,1773566632#u32,142131807#u32,457390543#u32,775738062#u32,407149060#u32,1692121370#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_57_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1545580060#u32,666169454#u32,462905305#u32,2070832458#u32,1873762300#u32,930261508#u32,705034056#u32,1032302632#u32,2135181392#u32,107510346#u32,2142574104#u32,837837786#u32,218388892#u32,1518209513#u32,1926007567#u32,1592081538#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_57_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [847109308#u32,1897439496#u32,9597005#u32,924665286#u32,1188982913#u32,1083068641#u32,170039717#u32,726645433#u32,1804065049#u32,836631207#u32,498865304#u32,1335973592#u32,1419195355#u32,1272847833#u32,250323815#u32,98987621#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_57_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [544079212#u32,470729407#u32,739967568#u32,124467408#u32,1642702274#u32,870002638#u32,1867077208#u32,2128924683#u32,1860349601#u32,149997850#u32,457736868#u32,1080273834#u32,292656860#u32,845973413#u32,2091495585#u32,425405827#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_57_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [1747405083#u32,901558961#u32,1910764690#u32,928699186#u32,687545864#u32,1465969880#u32,47758094#u32,1390539505#u32,184893665#u32,175573508#u32,1001947340#u32,1416140798#u32,1284076622#u32,999770408#u32,1912532123#u32,1194402472#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_57_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [391977824#u32,1449156311#u32,74159436#u32,2114910447#u32,1752996968#u32,380795313#u32,2075856358#u32,1495296143#u32,591666353#u32,397258811#u32,44490244#u32,706975411#u32,1328381768#u32,1928186353#u32,384933413#u32,1129069192#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_57_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1631000674#u32,1461649621#u32,160812182#u32,2029684157#u32,1151567172#u32,1810251024#u32,2015387356#u32,1222165994#u32,583858849#u32,779017517#u32,473346579#u32,975820610#u32,816297417#u32,1933253492#u32,1339111663#u32,994519190#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_57_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [983714665#u32,1611682250#u32,471656993#u32,1826318316#u32,772635417#u32,1196761602#u32,217918611#u32,1059244953#u32,1869521303#u32,2010021457#u32,1673108950#u32,644184122#u32,2141879582#u32,1338935954#u32,627646662#u32,830982019#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_57_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [1685460778#u32,3995855#u32,1483111238#u32,1402619575#u32,278429647#u32,360630061#u32,1070741863#u32,1759481187#u32,1467839219#u32,1856698611#u32,111411746#u32,2008042448#u32,1875937006#u32,1121013483#u32,814730349#u32,1739590163#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_57_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [1346051644#u32,1154234408#u32,1968977382#u32,318265912#u32,1230192082#u32,477868588#u32,1054239817#u32,2087884877#u32,55097649#u32,1871196982#u32,1419233166#u32,1229737551#u32,1433213773#u32,407511234#u32,717615081#u32,1319308985#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_57_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [171252238#u32,112398792#u32,748635501#u32,231228032#u32,209766452#u32,161610851#u32,481583823#u32,1586294045#u32,1715696162#u32,1243222142#u32,553980996#u32,114021065#u32,1699778298#u32,1243047364#u32,970687589#u32,1352693477#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_57_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1022340995#u32,317026858#u32,1701899068#u32,1129540194#u32,1882759682#u32,642918035#u32,582924873#u32,795715537#u32,770404808#u32,641916662#u32,545485162#u32,1230958907#u32,504478134#u32,1705215341#u32,1315248701#u32,51904931#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_57_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1020041663#u32,1163975217#u32,2103262848#u32,1070141841#u32,876640286#u32,396218684#u32,173191472#u32,233135199#u32,674516021#u32,1968856659#u32,1078006027#u32,563028275#u32,1773285259#u32,332847833#u32,1067071084#u32,874409527#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_57_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [298549050#u32,62170673#u32,1184764847#u32,1200995553#u32,338812944#u32,1130517798#u32,1157996857#u32,1934020731#u32,13735416#u32,1199480851#u32,666864318#u32,2045037626#u32,636653947#u32,847023849#u32,1732859912#u32,636954#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_57_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [329033374#u32,975278148#u32,1578178489#u32,225957357#u32,43548823#u32,502652768#u32,790529665#u32,1231887720#u32,278851010#u32,1382315443#u32,1951735005#u32,1631809052#u32,1188312548#u32,271938052#u32,506257377#u32,1985583406#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_57_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1655315904#u32,785761749#u32,548811618#u32,1963293633#u32,533854942#u32,1143625400#u32,905833996#u32,1448113846#u32,1524585346#u32,825776905#u32,1631294346#u32,533227708#u32,1762239266#u32,416579270#u32,162566731#u32,1244095497#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_57_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,1825776613#u32,369526834#u32,1655898863#u32,40149299#u32,231370585#u32,660847941#u32,945417929#u32,1519287229#u32,386683637#u32,784385603#u32,662344456#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_57_23 := by
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
    exact PV_RunJoin_OutputModel16.round_57_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_57_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_57_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_57_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_57_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_57_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_57_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_57_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_57_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_57_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_57_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_57_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_57_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_57_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_57_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_57_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_57_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_57_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_57_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_57_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_57_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_57_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_57_23
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
end R1Z.PV_RunJoin_ValidatorCell5719
