import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node07
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1155231487,231917266,23510830,1282340338,1179486231,882350493,608913733,1480730980,244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,1841894216]
def s1 : Fin 16 → M := ![1335352423,1756510165,1734216890,1081167761,1971471490,741263420,2027398946,639065760,1848255414,1021453443,364840457,2106865280,1436189558,1141047797,1760991139,214494897]
def s2 : Fin 16 → M := ![1250026087,1959328649,1742653529,1305640321,671371284,840284966,293514168,389027815,1593158250,1860170168,885498427,1572985052,62846925,1514321777,1261942842,1297376542]
def s3 : Fin 16 → M := ![1401555220,1495607327,1842512608,1860433344,1940037099,1234469588,1512302077,268948066,2147422774,1555925791,1746511770,45018007,706538192,1027321763,1114902430,476983785]
def s4 : Fin 16 → M := ![705216076,855412121,362916578,618950980,2018596646,1867010717,1476912866,2012588031,441300843,1832690343,2074896637,2069931000,918351620,1007082129,1365230374,690659978]
def s5 : Fin 16 → M := ![836094855,252804586,967162598,2005405457,1837713799,1759180876,511877635,440211560,1448969963,446342192,472106729,988743982,2109947929,616141470,789460657,857588974]
def s6 : Fin 16 → M := ![651783961,543566381,77603344,1869932682,2107570305,520368400,1638460586,547014224,1075323417,737729656,544231716,31953825,2035805107,1979465375,749558609,1447236222]
def s7 : Fin 16 → M := ![1089588757,1200846264,812486571,1694559670,337973147,393239695,1548411107,1306451867,859723851,537510883,1752292494,543644616,614713825,919946889,1423308856,967571473]
def s8 : Fin 16 → M := ![223876956,737560666,1161687544,2019985788,93015931,1533582228,1841229592,1545255304,59701333,1848030689,735383013,1512003246,1570700234,906309132,1618945911,1551123961]
def s9 : Fin 16 → M := ![2042690266,1804161192,1242491967,556609090,1810727974,1981596057,2003889001,1178692220,118436562,1716054570,332045741,889058194,520904630,186000209,1397680333,93110583]
def s10 : Fin 16 → M := ![322985384,931837749,1612660491,1354112917,728598467,768442411,975098826,1549534639,1402654611,350982489,1987582762,725257516,1475882575,1423289367,1080572379,221802918]
def s11 : Fin 16 → M := ![1677580718,218622560,364622146,408269185,820605253,844445152,425176185,1820237592,585432318,1091472468,904519390,2119170193,1531390248,1082334613,1919611794,1193495963]
def s12 : Fin 16 → M := ![1812513336,1147631933,1658253665,414602466,1051400456,1555229923,1649745411,1460098323,702418432,1173087071,1591412876,921218727,478455215,2126835486,824770888,83565860]
def s13 : Fin 16 → M := ![1895156475,717674217,739065967,1228452148,1538794991,831400935,822287908,674538135,1432772053,1380105527,1384222882,1900663944,2064991436,572988686,1728286420,58943394]
def s14 : Fin 16 → M := ![2129995600,525801198,1286258915,426968279,1381068674,225640059,351536273,28894681,666839770,927823785,2060634776,299421230,489283274,1003737368,1006282504,1546798859]
def s15 : Fin 16 → M := ![1372008022,2132935996,2032168981,1167524267,1918265955,922408448,2118877299,1308910735,1063279478,759338941,720720421,1823330441,463746457,1410403384,860826185,651601587]
def s16 : Fin 16 → M := ![1902464628,284442872,68361191,674120297,612732634,25140162,1531071034,317415330,1107293946,1416231189,1729810706,1859836240,411394724,1423992259,653717258,948275560]
def s17 : Fin 16 → M := ![187180782,455129130,307408640,719683799,777580036,572928850,1920319112,1157914555,170390644,1948617946,1970324074,935429389,914423123,597516706,28417577,328525885]
def s18 : Fin 16 → M := ![1337902780,1104125165,1263813315,1380247584,427185382,1225923047,1969665503,1741083557,984161997,1278984107,1773703278,1056947131,1180258915,2132244113,1975740020,250350573]
def s19 : Fin 16 → M := ![853894460,1084392433,360410251,1206290310,1250266677,267683197,732537601,1887948919,1398951358,982684316,1628742225,2056167139,689920154,1551328911,839736519,180356316]
def s20 : Fin 16 → M := ![971424634,412663613,932784370,1425165337,1202633755,1162418677,1180395032,1046394269,845201242,960796700,1551118241,1301099858,2027885289,1405791651,805847386,152395701]
def s21 : Fin 16 → M := ![1717208754,167971853,742591059,961576349,566478236,1895557907,593762668,848983819,539812502,1134020471,2096045824,873755684,2029557069,1832954058,1979273826,173790194]
def s22 : Fin 16 → M := ![1022889916,905518683,1657463916,1858316638,1965076020,2025527278,1217812598,330872598,780055561,1165008584,854646286,623342231,569623214,115388656,363123334,1862351607]
def s23 : Fin 16 → M := ![1966772867,1862185458,732026348,768495536,1089107776,21340238,1741078439,2033054791,1978207916,830209657,280979402,1869094098,22268226,464997283,1360427068,693114637]
theorem r1 : poseidonExternalLinear s0 = s1 := by
  funext i
  fin_cases i <;> rfl
#print axioms r1
theorem r2 : poseidonFullRound s1 (poseidonExternalInitial 0) = s2 := by
  funext i
  fin_cases i <;> rfl
#print axioms r2
theorem r3 : poseidonFullRound s2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s3 := by
  funext i
  fin_cases i <;> rfl
#print axioms r3
theorem r4 : poseidonFullRound s3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s4 := by
  funext i
  fin_cases i <;> rfl
#print axioms r4
theorem r5 : poseidonFullRound s4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s5 := by
  funext i
  fin_cases i <;> rfl
#print axioms r5
theorem r6 : poseidonInternalRound s5 (poseidonInternalConstants 0) = s6 := by
  funext i
  fin_cases i <;> rfl
#print axioms r6
theorem r7 : poseidonInternalRound s6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s7 := by
  funext i
  fin_cases i <;> rfl
#print axioms r7
theorem r8 : poseidonInternalRound s7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s8 := by
  funext i
  fin_cases i <;> rfl
#print axioms r8
theorem r9 : poseidonInternalRound s8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s9 := by
  funext i
  fin_cases i <;> rfl
#print axioms r9
theorem r10 : poseidonInternalRound s9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s10 := by
  funext i
  fin_cases i <;> rfl
#print axioms r10
theorem r11 : poseidonInternalRound s10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s11 := by
  funext i
  fin_cases i <;> rfl
#print axioms r11
theorem r12 : poseidonInternalRound s11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s12 := by
  funext i
  fin_cases i <;> rfl
#print axioms r12
theorem r13 : poseidonInternalRound s12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s13 := by
  funext i
  fin_cases i <;> rfl
#print axioms r13
theorem r14 : poseidonInternalRound s13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s14 := by
  funext i
  fin_cases i <;> rfl
#print axioms r14
theorem r15 : poseidonInternalRound s14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s15 := by
  funext i
  fin_cases i <;> rfl
#print axioms r15
theorem r16 : poseidonInternalRound s15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s16 := by
  funext i
  fin_cases i <;> rfl
#print axioms r16
theorem r17 : poseidonInternalRound s16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s17 := by
  funext i
  fin_cases i <;> rfl
#print axioms r17
theorem r18 : poseidonInternalRound s17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s18 := by
  funext i
  fin_cases i <;> rfl
#print axioms r18
theorem r19 : poseidonInternalRound s18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s19 := by
  funext i
  fin_cases i <;> rfl
#print axioms r19
theorem r20 : poseidonFullRound s19 (poseidonExternalFinal 0) = s20 := by
  funext i
  fin_cases i <;> rfl
#print axioms r20
theorem r21 : poseidonFullRound s20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s21 := by
  funext i
  fin_cases i <;> rfl
#print axioms r21
theorem r22 : poseidonFullRound s21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s22 := by
  funext i
  fin_cases i <;> rfl
#print axioms r22
theorem r23 : poseidonFullRound s22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s23 := by
  funext i
  fin_cases i <;> rfl
#print axioms r23
theorem permutation : poseidonPermutation s0 = s23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23]
#print axioms permutation
def left : Fin 8 → M := ![1155231487,231917266,23510830,1282340338,1179486231,882350493,608913733,1480730980]
def right : Fin 8 → M := ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587]
def output : Fin 8 → M := ![1966772867,1862185458,732026348,768495536,1089107776,21340238,1741078439,2033054791]
theorem source : nodeCompress left right = output := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then left ⟨l.val,h⟩
    else if l.val = 15 then right 7 - (1051521018 : M)
    else right ⟨l.val-8,by omega⟩) = s0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.PV_2TNV_Node07
