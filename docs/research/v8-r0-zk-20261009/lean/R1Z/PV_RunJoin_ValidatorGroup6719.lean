import R1Z.PV_RunJoin_IndexedPair19
import R1Z.PV_RunJoin_OutputCell6717
import R1Z.PV_RunJoin_OutputCell6817
import R1Z.PV_RunJoin_OutputCell6917
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell6719
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,778988106#u32,1148923135#u32,1488375597#u32,266199979#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_67_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [247221093#u32,1882404594#u32,801736090#u32,922705254#u32,1996626457#u32,2065221436#u32,680750056#u32,1128018994#u32,62274195#u32,788909709#u32,1036786325#u32,785373091#u32,1797691986#u32,908504063#u32,285453360#u32,1040486355#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_67_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1597006809#u32,176045052#u32,225393665#u32,746966554#u32,513927485#u32,36770549#u32,800510581#u32,70890565#u32,1073797784#u32,822526372#u32,826450753#u32,866789515#u32,1098866752#u32,1908881675#u32,1844587775#u32,896970698#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_67_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [534395316#u32,55344607#u32,2146484853#u32,877957084#u32,890044665#u32,1613105774#u32,918257613#u32,45505447#u32,29381498#u32,810777011#u32,2031692988#u32,1725966941#u32,1898536597#u32,1314516573#u32,463935981#u32,187383889#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_67_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [976428773#u32,1502371730#u32,1094641502#u32,1699653761#u32,1220393687#u32,1698249496#u32,1192882902#u32,1905029058#u32,937657903#u32,715748430#u32,1463677510#u32,1228820985#u32,812207458#u32,1154044899#u32,503282713#u32,1923407467#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_67_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [1447619884#u32,600939922#u32,148358660#u32,1356300561#u32,437102652#u32,843623276#u32,2142628583#u32,714683526#u32,2012773805#u32,277070714#u32,758187702#u32,2045109189#u32,2101155347#u32,1920120539#u32,2087983308#u32,468701097#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_67_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [387160320#u32,1683519012#u32,1379296410#u32,65330393#u32,284433012#u32,1695649624#u32,927217042#u32,1725168167#u32,1019588490#u32,1145721523#u32,77705724#u32,516110287#u32,1665751009#u32,1849545163#u32,1290622214#u32,271585394#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_67_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [1049126191#u32,1764108691#u32,691698852#u32,341911251#u32,208570128#u32,1441179899#u32,1834247612#u32,969686370#u32,1738897579#u32,1327523575#u32,194356116#u32,944416583#u32,801762369#u32,2034281101#u32,793837660#u32,356504527#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_67_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [351390834#u32,86427778#u32,1853200438#u32,1837447738#u32,2138363758#u32,2053844648#u32,1183667849#u32,252704651#u32,1857877205#u32,1013421708#u32,1921969994#u32,1182078455#u32,1502137056#u32,1185160078#u32,472829503#u32,1875888493#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_67_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1499806602#u32,765954234#u32,90960038#u32,1586866467#u32,606567344#u32,1328786119#u32,2049675625#u32,1820238591#u32,117123879#u32,269962417#u32,1681779660#u32,2044737798#u32,1104991898#u32,795108234#u32,262167655#u32,1911463895#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_67_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [1651839192#u32,1922111692#u32,1338077534#u32,1061172385#u32,1713728916#u32,941898892#u32,173784401#u32,1687310344#u32,1115628441#u32,1547059506#u32,1016644404#u32,1215954766#u32,1606213769#u32,1573660612#u32,1931288498#u32,1690399727#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_67_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [625796293#u32,1563993880#u32,170553609#u32,1739088081#u32,466811634#u32,1827362578#u32,908015726#u32,255561854#u32,708401934#u32,552124676#u32,1303666736#u32,178026331#u32,112772667#u32,1956166961#u32,2055274856#u32,1586976718#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_67_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [1460532579#u32,808286725#u32,1732883710#u32,1905677875#u32,831302270#u32,564806682#u32,383508666#u32,567865972#u32,1872910870#u32,1001772846#u32,611685722#u32,443188288#u32,1807496346#u32,37834041#u32,1403604333#u32,717459483#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_67_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1834536362#u32,437030610#u32,947027658#u32,809004444#u32,1984194751#u32,75716209#u32,1163602962#u32,1612427741#u32,990650428#u32,532038468#u32,1077181936#u32,304289818#u32,1886547899#u32,1026381293#u32,278259830#u32,2046454355#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_67_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [2086298854#u32,775061149#u32,84602208#u32,1426564668#u32,1179203018#u32,1549489883#u32,1066103324#u32,454190907#u32,439750150#u32,1248408586#u32,1713222092#u32,1168609807#u32,1646095335#u32,1772179041#u32,140574817#u32,2121917375#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_67_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [379051861#u32,1755699303#u32,1149842570#u32,244445885#u32,1824327710#u32,2672518#u32,736206170#u32,2131568791#u32,1434082532#u32,598172767#u32,825920763#u32,865358463#u32,1743802961#u32,235654811#u32,983818795#u32,506681022#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_67_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [1348154460#u32,419283907#u32,963269744#u32,1788851791#u32,373304402#u32,853828539#u32,747345574#u32,1940001114#u32,1837522352#u32,1471957666#u32,445372645#u32,1971315149#u32,983704919#u32,603894369#u32,560834047#u32,118892482#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_67_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [485069371#u32,28200878#u32,1535456459#u32,321873194#u32,447868540#u32,385271713#u32,2049138869#u32,1362420388#u32,736060504#u32,620441242#u32,403972287#u32,1724738202#u32,760969875#u32,357096938#u32,1001401688#u32,275946007#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_67_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1468046195#u32,1107031781#u32,2002260174#u32,218840032#u32,366811929#u32,800727370#u32,79281654#u32,226906208#u32,805294947#u32,997998977#u32,282108920#u32,385307665#u32,799019662#u32,2009608667#u32,1459217127#u32,1516554268#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_67_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1486708460#u32,2111941966#u32,714463239#u32,1880270313#u32,1791921970#u32,931646223#u32,1394439466#u32,494521968#u32,1003448345#u32,942094304#u32,2121635567#u32,824625480#u32,1043825233#u32,1214034509#u32,760843619#u32,67267379#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_67_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1495053234#u32,1069315666#u32,670603262#u32,1732279548#u32,2146949908#u32,493638875#u32,6649147#u32,1051911928#u32,406209868#u32,2126898575#u32,379066421#u32,312733530#u32,182595336#u32,1337836294#u32,2049864943#u32,2095118953#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_67_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1029447878#u32,1632005007#u32,533034052#u32,516540676#u32,1431421274#u32,548367277#u32,403555288#u32,1665452766#u32,228355612#u32,1759217531#u32,1178426006#u32,804543992#u32,1709228113#u32,1177051584#u32,438428961#u32,1683090010#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_67_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [2018142491#u32,956957230#u32,846593235#u32,788408325#u32,2078087138#u32,325260918#u32,610294345#u32,1315020113#u32,1367367437#u32,1616941391#u32,1093157053#u32,1989945347#u32,1871584034#u32,1638169625#u32,319742210#u32,485005322#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_67_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,983928879#u32,1739454800#u32,712455604#u32,595030347#u32,1335028102#u32,830891998#u32,1283996981#u32,843960883#u32,784648266#u32,1975382205#u32,862783498#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_67_23 := by
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
    exact PV_RunJoin_OutputModel16.round_67_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_67_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_67_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_67_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_67_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_67_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_67_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_67_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_67_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_67_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_67_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_67_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_67_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_67_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_67_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_67_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_67_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_67_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_67_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_67_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_67_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_67_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_67_23
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
end R1Z.PV_RunJoin_ValidatorCell6719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell6819
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,983928879#u32,1739454800#u32,712455604#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_68_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [587133138#u32,958946225#u32,1729429179#u32,2072329559#u32,1743205265#u32,1671790696#u32,385786727#u32,796525354#u32,1348211383#u32,1674362534#u32,728898556#u32,750334179#u32,1116319002#u32,1878932813#u32,1254776669#u32,1383052863#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_68_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [1234441235#u32,1004779541#u32,1226132569#u32,95538018#u32,1302421177#u32,1275284291#u32,585228246#u32,1826317500#u32,1199438387#u32,505494966#u32,203674981#u32,477915822#u32,7540506#u32,335529508#u32,690963672#u32,852666130#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_68_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [358716656#u32,1749021438#u32,1580097440#u32,775680468#u32,2147329568#u32,1058908#u32,653434895#u32,207617771#u32,378012800#u32,1223956965#u32,490707617#u32,1492922896#u32,1719708489#u32,1223424491#u32,376432471#u32,1314356118#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_68_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [156653363#u32,669309598#u32,159472115#u32,331466794#u32,413429369#u32,299350387#u32,1701378751#u32,804166037#u32,1813001790#u32,2043618571#u32,1835666254#u32,351489786#u32,86772409#u32,1075260710#u32,1426114438#u32,102871072#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_68_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [368644008#u32,1251072450#u32,43271729#u32,181959010#u32,533163064#u32,629012540#u32,1079557614#u32,361329616#u32,107073431#u32,909980095#u32,1907489514#u32,659301270#u32,1316317251#u32,174658953#u32,1811125405#u32,1372434124#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_68_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [2118004336#u32,186240129#u32,1169194784#u32,1810487366#u32,1052988544#u32,409433731#u32,1268756622#u32,585426633#u32,1903148612#u32,2109321770#u32,141794892#u32,46225320#u32,1838179931#u32,99235827#u32,181853874#u32,1867814489#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_68_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [8900140#u32,1600257626#u32,1604923418#u32,66032373#u32,1247991261#u32,1522506252#u32,1212040108#u32,226616363#u32,203904075#u32,234511573#u32,583098909#u32,1774367281#u32,1628679485#u32,1648686286#u32,1134640304#u32,1789005954#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_68_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [1801992965#u32,540532492#u32,2638055#u32,1351888005#u32,334270366#u32,1825538428#u32,1218336323#u32,558820216#u32,1417676349#u32,993179085#u32,1180587463#u32,1811480041#u32,914200822#u32,2114556371#u32,1596859474#u32,1364768245#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_68_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [699231716#u32,2079709541#u32,1544453159#u32,504278128#u32,2065856330#u32,683020839#u32,1871233739#u32,796448874#u32,465639726#u32,242468816#u32,1427445900#u32,1805424600#u32,249350137#u32,1077082462#u32,1843878279#u32,296983819#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_68_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [745783016#u32,880736871#u32,1889933648#u32,818139842#u32,295492441#u32,1139426166#u32,698448509#u32,381631385#u32,420853789#u32,743502110#u32,216748970#u32,33992309#u32,1367884984#u32,1994440986#u32,1699548904#u32,1435780200#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_68_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [1352030590#u32,1792024745#u32,396187876#u32,2036363595#u32,1127743755#u32,1962237354#u32,1786803692#u32,1713376397#u32,1093481691#u32,121783451#u32,1671417513#u32,557348483#u32,1055406756#u32,1721229746#u32,1036356495#u32,2058998122#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_68_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [1084317383#u32,167037411#u32,1314872065#u32,78016105#u32,954511765#u32,1853522919#u32,1865639635#u32,656919724#u32,901715706#u32,1634288711#u32,509562966#u32,646765920#u32,645478643#u32,395402373#u32,1693214462#u32,1888460460#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_68_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1861466473#u32,799101257#u32,1114324329#u32,944128266#u32,1825707025#u32,223659492#u32,202990050#u32,1872736889#u32,87557276#u32,250662697#u32,586014809#u32,1937935415#u32,1288368388#u32,2093863726#u32,1496050770#u32,1146710149#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_68_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [1079691946#u32,1394259329#u32,676323083#u32,76703842#u32,168428743#u32,2026226297#u32,648388731#u32,191234736#u32,1065071165#u32,340299094#u32,1526384975#u32,1279058600#u32,26867563#u32,407184031#u32,430095716#u32,201256171#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_68_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [808258166#u32,26728845#u32,2132599329#u32,1086768531#u32,2127383107#u32,987319210#u32,53556085#u32,134074385#u32,1817592522#u32,1997175347#u32,430072547#u32,2091363730#u32,1835697265#u32,1998909485#u32,221199790#u32,459815945#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_68_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [298983674#u32,168519065#u32,112021584#u32,193897050#u32,2128469547#u32,906512051#u32,1855584940#u32,132616272#u32,865399160#u32,317571066#u32,301930713#u32,55360417#u32,1493288806#u32,1149175710#u32,659200315#u32,1149027036#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_68_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [1767992021#u32,2050321685#u32,2105845788#u32,509907173#u32,1729689820#u32,1353609907#u32,1130978584#u32,1779309440#u32,983745456#u32,1575616930#u32,1821207564#u32,1004804070#u32,689364413#u32,840018364#u32,1019719367#u32,856068214#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_68_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [186201765#u32,2109827824#u32,2123714068#u32,2099134831#u32,1012122817#u32,242428181#u32,1891082475#u32,118677008#u32,1424872981#u32,1837998230#u32,960246079#u32,1158309207#u32,1598269472#u32,1845171939#u32,1525660322#u32,335700968#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_68_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1316609161#u32,557462174#u32,547578839#u32,401722733#u32,102165945#u32,179001599#u32,980215081#u32,1747995568#u32,442749570#u32,823746184#u32,339592567#u32,1238253646#u32,410836862#u32,1764867754#u32,13247133#u32,123793330#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_68_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [430616544#u32,306521884#u32,45264667#u32,1581280722#u32,2006851348#u32,1671171874#u32,2042947347#u32,95556525#u32,214711301#u32,2069431795#u32,1663590141#u32,1120413480#u32,420560467#u32,1752019900#u32,557447070#u32,247466706#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_68_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [72644080#u32,1731387381#u32,534650503#u32,1424074034#u32,1477060747#u32,562194305#u32,87027992#u32,1966031473#u32,767393486#u32,1798301362#u32,857636565#u32,1010937790#u32,315664023#u32,817385252#u32,885178772#u32,15817026#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_68_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1807236164#u32,1618348919#u32,1753444092#u32,2098962065#u32,1154374574#u32,1490534393#u32,908852502#u32,366680569#u32,1694070040#u32,1204788813#u32,1000047875#u32,658033626#u32,496399026#u32,335377#u32,836183486#u32,1507091657#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_68_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,2116907504#u32,1823343454#u32,355665714#u32,826222920#u32,2018074965#u32,1740474058#u32,61745978#u32,1524656651#u32,972433596#u32,772885858#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_68_23 := by
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
    exact PV_RunJoin_OutputModel16.round_68_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_68_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_68_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_68_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_68_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_68_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_68_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_68_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_68_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_68_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_68_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_68_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_68_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_68_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_68_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_68_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_68_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_68_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_68_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_68_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_68_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_68_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_68_23
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
end R1Z.PV_RunJoin_ValidatorCell6819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidatorCell6919
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def s0 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,2116907504#u32,1823343454#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
theorem lift0 : liftA (K := PV_RunJoin_FixtureRecords.M) s0 = PV_RunJoin_OutputModel16.s_69_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift0
theorem canon0 : Canonical s0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon0
def s1 : State := Array.make 16#usize [334147827#u32,1319053574#u32,216228222#u32,366289647#u32,1134897724#u32,1296723166#u32,1815361549#u32,558672432#u32,108327046#u32,582790359#u32,228048414#u32,1420343242#u32,1684439570#u32,1098428265#u32,1327321093#u32,2035375616#u32]
theorem lift1 : liftA (K := PV_RunJoin_FixtureRecords.M) s1 = PV_RunJoin_OutputModel16.s_69_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift1
theorem canon1 : Canonical s1 := by
  intro i
  fin_cases i <;> decide
#print axioms canon1
def s2 : State := Array.make 16#usize [2003473132#u32,672440074#u32,301832028#u32,1304504753#u32,326255720#u32,377937585#u32,618850005#u32,2127519529#u32,790519077#u32,104250811#u32,1715035706#u32,800438303#u32,2032813608#u32,1688747744#u32,1234573354#u32,176552486#u32]
theorem lift2 : liftA (K := PV_RunJoin_FixtureRecords.M) s2 = PV_RunJoin_OutputModel16.s_69_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift2
theorem canon2 : Canonical s2 := by
  intro i
  fin_cases i <;> decide
#print axioms canon2
def s3 : State := Array.make 16#usize [1266169738#u32,1331292488#u32,578638865#u32,668196354#u32,696551770#u32,676024590#u32,179100847#u32,720499829#u32,540913910#u32,1229707444#u32,1471546299#u32,802172943#u32,828582636#u32,370781038#u32,639517021#u32,55184556#u32]
theorem lift3 : liftA (K := PV_RunJoin_FixtureRecords.M) s3 = PV_RunJoin_OutputModel16.s_69_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift3
theorem canon3 : Canonical s3 := by
  intro i
  fin_cases i <;> decide
#print axioms canon3
def s4 : State := Array.make 16#usize [689017256#u32,111640396#u32,1341504224#u32,1898056281#u32,1795505240#u32,665615062#u32,478520553#u32,1515685285#u32,1967945712#u32,792358898#u32,713151199#u32,554480056#u32,768752506#u32,449852035#u32,1693874491#u32,556533314#u32]
theorem lift4 : liftA (K := PV_RunJoin_FixtureRecords.M) s4 = PV_RunJoin_OutputModel16.s_69_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4
theorem canon4 : Canonical s4 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4
def s5 : State := Array.make 16#usize [852149114#u32,1882851786#u32,890569961#u32,1710635450#u32,1149474560#u32,114886883#u32,240882147#u32,680552588#u32,1916355370#u32,434999145#u32,357060773#u32,199451383#u32,702246401#u32,1554154902#u32,926212065#u32,598588541#u32]
theorem lift5 : liftA (K := PV_RunJoin_FixtureRecords.M) s5 = PV_RunJoin_OutputModel16.s_69_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5
theorem canon5 : Canonical s5 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5
def s6 : State := Array.make 16#usize [1406986780#u32,1423905152#u32,1322193288#u32,2088627872#u32,146915258#u32,1379243494#u32,806831129#u32,146746058#u32,21404968#u32,1379168489#u32,99064928#u32,450132274#u32,1382363692#u32,101365255#u32,1419099882#u32,555896593#u32]
theorem lift6 : liftA (K := PV_RunJoin_FixtureRecords.M) s6 = PV_RunJoin_OutputModel16.s_69_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift6
theorem canon6 : Canonical s6 := by
  intro i
  fin_cases i <;> decide
#print axioms canon6
def s7 : State := Array.make 16#usize [1967315512#u32,1280186187#u32,353183964#u32,1768341582#u32,1031603099#u32,449340469#u32,2052557046#u32,658094159#u32,448633292#u32,736096111#u32,367035898#u32,1057106213#u32,498375268#u32,619759824#u32,1457805920#u32,1182812175#u32]
theorem lift7 : liftA (K := PV_RunJoin_FixtureRecords.M) s7 = PV_RunJoin_OutputModel16.s_69_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift7
theorem canon7 : Canonical s7 := by
  intro i
  fin_cases i <;> decide
#print axioms canon7
def s8 : State := Array.make 16#usize [2133641380#u32,1298603457#u32,724785198#u32,649332657#u32,1828791121#u32,765413833#u32,1275733332#u32,1334254153#u32,1608903824#u32,1627944397#u32,53538597#u32,598433366#u32,342199779#u32,860690670#u32,776559962#u32,1227395958#u32]
theorem lift8 : liftA (K := PV_RunJoin_FixtureRecords.M) s8 = PV_RunJoin_OutputModel16.s_69_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift8
theorem canon8 : Canonical s8 := by
  intro i
  fin_cases i <;> decide
#print axioms canon8
def s9 : State := Array.make 16#usize [1705471128#u32,1621005526#u32,1771972465#u32,772249050#u32,2067829155#u32,1831605162#u32,343679400#u32,1962805628#u32,103661429#u32,464340183#u32,1458834222#u32,1226627978#u32,1156832302#u32,1500713147#u32,1105503582#u32,648939878#u32]
theorem lift9 : liftA (K := PV_RunJoin_FixtureRecords.M) s9 = PV_RunJoin_OutputModel16.s_69_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift9
theorem canon9 : Canonical s9 := by
  intro i
  fin_cases i <;> decide
#print axioms canon9
def s10 : State := Array.make 16#usize [771206599#u32,415775142#u32,191230899#u32,1883765816#u32,305017327#u32,183164797#u32,1202575828#u32,2007761929#u32,1326014293#u32,1701739526#u32,139878279#u32,98717171#u32,867137036#u32,2086179208#u32,181986996#u32,1099952683#u32]
theorem lift10 : liftA (K := PV_RunJoin_FixtureRecords.M) s10 = PV_RunJoin_OutputModel16.s_69_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift10
theorem canon10 : Canonical s10 := by
  intro i
  fin_cases i <;> decide
#print axioms canon10
def s11 : State := Array.make 16#usize [170979544#u32,1856785694#u32,1823472350#u32,386139228#u32,1733665521#u32,76680010#u32,1268731402#u32,1088755188#u32,1519631943#u32,1147148867#u32,794963899#u32,2059617332#u32,1151705188#u32,2051428772#u32,1228807761#u32,1208981144#u32]
theorem lift11 : liftA (K := PV_RunJoin_FixtureRecords.M) s11 = PV_RunJoin_OutputModel16.s_69_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift11
theorem canon11 : Canonical s11 := by
  intro i
  fin_cases i <;> decide
#print axioms canon11
def s12 : State := Array.make 16#usize [2091571101#u32,2051021192#u32,1693696551#u32,1738792410#u32,1178657784#u32,1421115658#u32,2138934716#u32,1155090826#u32,1433595972#u32,1806569458#u32,340965861#u32,1071061954#u32,1067474323#u32,536676749#u32,448566696#u32,573332617#u32]
theorem lift12 : liftA (K := PV_RunJoin_FixtureRecords.M) s12 = PV_RunJoin_OutputModel16.s_69_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift12
theorem canon12 : Canonical s12 := by
  intro i
  fin_cases i <;> decide
#print axioms canon12
def s13 : State := Array.make 16#usize [1716584415#u32,1138320312#u32,327208575#u32,1747501466#u32,2074110451#u32,350313178#u32,961216975#u32,2146151633#u32,51473541#u32,2007579910#u32,343989970#u32,995455530#u32,1431026199#u32,201103918#u32,342713580#u32,639798920#u32]
theorem lift13 : liftA (K := PV_RunJoin_FixtureRecords.M) s13 = PV_RunJoin_OutputModel16.s_69_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift13
theorem canon13 : Canonical s13 := by
  intro i
  fin_cases i <;> decide
#print axioms canon13
def s14 : State := Array.make 16#usize [451500082#u32,137977488#u32,1801557973#u32,1694695746#u32,560155255#u32,309700730#u32,1841312965#u32,1061891927#u32,1293303130#u32,1839006150#u32,1205551995#u32,461546050#u32,1000534058#u32,1793818837#u32,1993740100#u32,1390954268#u32]
theorem lift14 : liftA (K := PV_RunJoin_FixtureRecords.M) s14 = PV_RunJoin_OutputModel16.s_69_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift14
theorem canon14 : Canonical s14 := by
  intro i
  fin_cases i <;> decide
#print axioms canon14
def s15 : State := Array.make 16#usize [464320941#u32,2085411539#u32,1255582703#u32,136282447#u32,2133708797#u32,460194790#u32,739906815#u32,1189040675#u32,2133993872#u32,286606111#u32,1629579906#u32,506961844#u32,1377356588#u32,1414066617#u32,2075521817#u32,993010196#u32]
theorem lift15 : liftA (K := PV_RunJoin_FixtureRecords.M) s15 = PV_RunJoin_OutputModel16.s_69_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift15
theorem canon15 : Canonical s15 := by
  intro i
  fin_cases i <;> decide
#print axioms canon15
def s16 : State := Array.make 16#usize [97141199#u32,168014128#u32,593767995#u32,775216024#u32,119887436#u32,1150751935#u32,284784199#u32,1166761791#u32,650878683#u32,586806654#u32,325116261#u32,129112611#u32,656173794#u32,1243955328#u32,121885202#u32,801852604#u32]
theorem lift16 : liftA (K := PV_RunJoin_FixtureRecords.M) s16 = PV_RunJoin_OutputModel16.s_69_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift16
theorem canon16 : Canonical s16 := by
  intro i
  fin_cases i <;> decide
#print axioms canon16
def s17 : State := Array.make 16#usize [428507546#u32,109566696#u32,1129088558#u32,894933017#u32,900652056#u32,1173714352#u32,464712348#u32,1599863194#u32,1649645406#u32,1987684349#u32,638547#u32,505830062#u32,165704575#u32,1285836490#u32,1703751931#u32,1228966222#u32]
theorem lift17 : liftA (K := PV_RunJoin_FixtureRecords.M) s17 = PV_RunJoin_OutputModel16.s_69_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift17
theorem canon17 : Canonical s17 := by
  intro i
  fin_cases i <;> decide
#print axioms canon17
def s18 : State := Array.make 16#usize [1657531361#u32,135923530#u32,137050303#u32,1458605255#u32,789122341#u32,1625917290#u32,2012250088#u32,1485869841#u32,727571396#u32,2067409486#u32,680228962#u32,1732055078#u32,268570330#u32,356831924#u32,437260783#u32,182501091#u32]
theorem lift18 : liftA (K := PV_RunJoin_FixtureRecords.M) s18 = PV_RunJoin_OutputModel16.s_69_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift18
theorem canon18 : Canonical s18 := by
  intro i
  fin_cases i <;> decide
#print axioms canon18
def s19 : State := Array.make 16#usize [1040348469#u32,1520106693#u32,1658283769#u32,776153242#u32,1254710950#u32,1629056039#u32,1351676569#u32,1990572519#u32,24041383#u32,212550770#u32,6454976#u32,595812963#u32,341588348#u32,120455198#u32,1534627723#u32,291769149#u32]
theorem lift19 : liftA (K := PV_RunJoin_FixtureRecords.M) s19 = PV_RunJoin_OutputModel16.s_69_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift19
theorem canon19 : Canonical s19 := by
  intro i
  fin_cases i <;> decide
#print axioms canon19
def s20 : State := Array.make 16#usize [1947288544#u32,253726461#u32,1994388658#u32,1877143073#u32,1301686200#u32,806559524#u32,862098367#u32,688072657#u32,2131461632#u32,1036493905#u32,1048530138#u32,1500993586#u32,2069182824#u32,269867978#u32,104203141#u32,107355017#u32]
theorem lift20 : liftA (K := PV_RunJoin_FixtureRecords.M) s20 = PV_RunJoin_OutputModel16.s_69_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift20
theorem canon20 : Canonical s20 := by
  intro i
  fin_cases i <;> decide
#print axioms canon20
def s21 : State := Array.make 16#usize [1770401833#u32,1414397651#u32,1197233581#u32,398342380#u32,270787152#u32,1726182607#u32,567640451#u32,1326189579#u32,216789563#u32,253899857#u32,1729711937#u32,612856272#u32,1993055998#u32,1372587754#u32,1300192351#u32,1747840618#u32]
theorem lift21 : liftA (K := PV_RunJoin_FixtureRecords.M) s21 = PV_RunJoin_OutputModel16.s_69_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift21
theorem canon21 : Canonical s21 := by
  intro i
  fin_cases i <;> decide
#print axioms canon21
def s22 : State := Array.make 16#usize [1424957577#u32,427815666#u32,2017419695#u32,1362551741#u32,2023634830#u32,192946337#u32,290068399#u32,744930677#u32,1285850347#u32,493693440#u32,85132181#u32,112858894#u32,1450752626#u32,864293856#u32,527203632#u32,406576053#u32]
theorem lift22 : liftA (K := PV_RunJoin_FixtureRecords.M) s22 = PV_RunJoin_OutputModel16.s_69_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift22
theorem canon22 : Canonical s22 := by
  intro i
  fin_cases i <;> decide
#print axioms canon22
def s23 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,361707637#u32,1111542572#u32,2084776284#u32,596177238#u32,1704769512#u32,2057721071#u32,1626202319#u32,497648896#u32,1992516100#u32,1820778629#u32]
theorem lift23 : liftA (K := PV_RunJoin_FixtureRecords.M) s23 = PV_RunJoin_OutputModel16.s_69_23 := by
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
    exact PV_RunJoin_OutputModel16.round_69_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := by
  apply PV_RunJoin_IndexedTarget19.round s1 s2 canon1 canon2 ⟨0,by decide⟩
  rw [lift1,lift2]
  exact PV_RunJoin_OutputModel16.round_69_2
#print axioms step0
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := by
  apply PV_RunJoin_IndexedTarget19.round s2 s3 canon2 canon3 ⟨1,by decide⟩
  rw [lift2,lift3]
  exact PV_RunJoin_OutputModel16.round_69_3
#print axioms step1
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := by
  apply PV_RunJoin_IndexedTarget19.round s3 s4 canon3 canon4 ⟨2,by decide⟩
  rw [lift3,lift4]
  exact PV_RunJoin_OutputModel16.round_69_4
#print axioms step2
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := by
  apply PV_RunJoin_IndexedTarget19.round s4 s5 canon4 canon5 ⟨3,by decide⟩
  rw [lift4,lift5]
  exact PV_RunJoin_OutputModel16.round_69_5
#print axioms step3
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := by
  apply PV_RunJoin_IndexedTarget19.round s5 s6 canon5 canon6 ⟨4,by decide⟩
  rw [lift5,lift6]
  exact PV_RunJoin_OutputModel16.round_69_6
#print axioms step4
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := by
  apply PV_RunJoin_IndexedTarget19.round s6 s7 canon6 canon7 ⟨5,by decide⟩
  rw [lift6,lift7]
  exact PV_RunJoin_OutputModel16.round_69_7
#print axioms step5
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := by
  apply PV_RunJoin_IndexedTarget19.round s7 s8 canon7 canon8 ⟨6,by decide⟩
  rw [lift7,lift8]
  exact PV_RunJoin_OutputModel16.round_69_8
#print axioms step6
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := by
  apply PV_RunJoin_IndexedTarget19.round s8 s9 canon8 canon9 ⟨7,by decide⟩
  rw [lift8,lift9]
  exact PV_RunJoin_OutputModel16.round_69_9
#print axioms step7
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := by
  apply PV_RunJoin_IndexedTarget19.round s9 s10 canon9 canon10 ⟨8,by decide⟩
  rw [lift9,lift10]
  exact PV_RunJoin_OutputModel16.round_69_10
#print axioms step8
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := by
  apply PV_RunJoin_IndexedTarget19.round s10 s11 canon10 canon11 ⟨9,by decide⟩
  rw [lift10,lift11]
  exact PV_RunJoin_OutputModel16.round_69_11
#print axioms step9
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := by
  apply PV_RunJoin_IndexedTarget19.round s11 s12 canon11 canon12 ⟨10,by decide⟩
  rw [lift11,lift12]
  exact PV_RunJoin_OutputModel16.round_69_12
#print axioms step10
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := by
  apply PV_RunJoin_IndexedTarget19.round s12 s13 canon12 canon13 ⟨11,by decide⟩
  rw [lift12,lift13]
  exact PV_RunJoin_OutputModel16.round_69_13
#print axioms step11
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := by
  apply PV_RunJoin_IndexedTarget19.round s13 s14 canon13 canon14 ⟨12,by decide⟩
  rw [lift13,lift14]
  exact PV_RunJoin_OutputModel16.round_69_14
#print axioms step12
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := by
  apply PV_RunJoin_IndexedTarget19.round s14 s15 canon14 canon15 ⟨13,by decide⟩
  rw [lift14,lift15]
  exact PV_RunJoin_OutputModel16.round_69_15
#print axioms step13
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := by
  apply PV_RunJoin_IndexedTarget19.round s15 s16 canon15 canon16 ⟨14,by decide⟩
  rw [lift15,lift16]
  exact PV_RunJoin_OutputModel16.round_69_16
#print axioms step14
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := by
  apply PV_RunJoin_IndexedTarget19.round s16 s17 canon16 canon17 ⟨15,by decide⟩
  rw [lift16,lift17]
  exact PV_RunJoin_OutputModel16.round_69_17
#print axioms step15
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := by
  apply PV_RunJoin_IndexedTarget19.round s17 s18 canon17 canon18 ⟨16,by decide⟩
  rw [lift17,lift18]
  exact PV_RunJoin_OutputModel16.round_69_18
#print axioms step16
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := by
  apply PV_RunJoin_IndexedTarget19.round s18 s19 canon18 canon19 ⟨17,by decide⟩
  rw [lift18,lift19]
  exact PV_RunJoin_OutputModel16.round_69_19
#print axioms step17
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := by
  apply PV_RunJoin_IndexedTarget19.round s19 s20 canon19 canon20 ⟨18,by decide⟩
  rw [lift19,lift20]
  exact PV_RunJoin_OutputModel16.round_69_20
#print axioms step18
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := by
  apply PV_RunJoin_IndexedTarget19.round s20 s21 canon20 canon21 ⟨19,by decide⟩
  rw [lift20,lift21]
  exact PV_RunJoin_OutputModel16.round_69_21
#print axioms step19
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := by
  apply PV_RunJoin_IndexedTarget19.round s21 s22 canon21 canon22 ⟨20,by decide⟩
  rw [lift21,lift22]
  exact PV_RunJoin_OutputModel16.round_69_22
#print axioms step20
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := by
  apply PV_RunJoin_IndexedTarget19.round s22 s23 canon22 canon23 ⟨21,by decide⟩
  rw [lift22,lift23]
  exact PV_RunJoin_OutputModel16.round_69_23
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
end R1Z.PV_RunJoin_ValidatorCell6919
