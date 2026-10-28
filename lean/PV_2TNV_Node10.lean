import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node10
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1197839198,449684346,391417085,13476115,411598282,1584375671,1644734677,28127165,1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,602005867]
def s1 : Fin 16 → M := ![1719730736,554749838,1872140381,1552522094,524324227,1517528104,476211830,1611110363,1457420303,2051929469,1086238293,40013877,1328924420,1552218302,14632047,1578460684]
def s2 : Fin 16 → M := ![1646088540,1955586401,408620464,1535435438,23847969,1265324949,489228535,1953474912,1358262377,700905538,229366352,848008743,1442569544,1908209453,1564328906,604023294]
def s3 : Fin 16 → M := ![484706952,812801657,576428836,99324939,1920778209,1307966905,1110479298,185680065,1173937587,1019000721,678685025,2121057486,1646370598,587038084,225402315,310903981]
def s4 : Fin 16 → M := ![1692828950,1873197950,331455462,2094682520,817854892,1008975850,573858158,226507314,869002420,1449068359,1579487133,370588910,871703578,341215250,199794995,140533592]
def s5 : Fin 16 → M := ![570175199,2104273908,1276486884,488128947,1126301293,575765839,1758062460,885199464,1421477636,528664236,740856686,2091873782,2044440682,564370074,2036707826,909052170]
def s6 : Fin 16 → M := ![1185964812,1514410871,1963110731,1362652751,1978096366,32455799,1981044508,228327837,970648023,1604195265,2133139683,1412880152,1390724601,1132329044,902881512,1709298656]
def s7 : Fin 16 → M := ![1749385783,1742711040,2007037984,1383943879,1020685568,747592953,1344698662,1956379855,2064679234,732911432,572466562,2064457743,643484226,196130632,2114964313,1635541324]
def s8 : Fin 16 → M := ![447636883,948255678,1072136959,446352860,928578241,429613651,1433712529,2007287479,1491481656,2147277588,1295752142,581341727,703454292,2121767061,911380685,837965238]
def s9 : Fin 16 → M := ![781245124,519987774,1716006014,1357143536,557907083,3099571,353376437,1336595579,1502823128,1666464639,1424515305,1335565012,570667259,1285465531,786422994,1009748580]
def s10 : Fin 16 → M := ![91707069,1215086531,1979627138,1828705607,863388127,744691893,1265726506,337869933,1930414558,2108284235,1257374764,1528539000,529384966,1390232532,400002149,869455332]
def s11 : Fin 16 → M := ![379848423,825582651,1422266749,482867607,75150195,788148173,1459038666,1906819009,1890423786,312864883,819549903,591409115,562654299,968740326,788216911,1051528221]
def s12 : Fin 16 → M := ![1145746909,1800552966,1672020166,758957096,1576171875,700439201,419567393,604819012,283562812,1611485424,527965010,1025151539,1739081261,764836522,1480887494,1178229541]
def s13 : Fin 16 → M := ![768820075,1106932810,502936529,194724581,1178336609,1923472472,1995118185,1507574613,1242681428,1677271811,924154687,2144037350,1601039405,1968359694,487295624,835567288]
def s14 : Fin 16 → M := ![529900386,501332950,400273198,173298464,231158424,105188634,961156297,1389894904,1691316693,1426738003,835994948,310753157,426573671,237699637,556491927,446671655]
def s15 : Fin 16 → M := ![2093924035,616624863,915838309,808485769,1964559305,1798310057,807522359,1021736242,1855463917,288000691,1475627159,1649903961,650911076,1198292510,959109172,839281736]
def s16 : Fin 16 → M := ![1683686372,420018038,1635069793,889852604,487482086,659066676,2021788546,770003253,1079573381,517126073,1164600150,1826463969,2012515913,332376141,1617051073,1620076707]
def s17 : Fin 16 → M := ![1686951096,626941043,1329578944,1618849774,1959296046,14571586,479647067,95007316,953362365,1594695226,904052520,1717797528,505324282,1986572004,724976991,1962485277]
def s18 : Fin 16 → M := ![1211880613,149121663,33854861,1702612422,164163459,1902809643,1985984882,1307681550,1293479108,1889749193,1853992890,464427736,937710995,255740224,104118594,161675262]
def s19 : Fin 16 → M := ![958959167,1834603696,1753191755,2053480780,851306058,2065665263,812488847,1625239000,1894567038,129971219,1798657445,1310977447,1864947754,1992716752,1092055142,1551138167]
def s20 : Fin 16 → M := ![1997917058,579823661,1805376641,341024323,184367986,824307939,1824591239,2002851296,1656151567,1253545493,2084689350,1634755866,72980927,65211410,1836948894,642586589]
def s21 : Fin 16 → M := ![1996256743,171773153,2048661057,1339653143,695110894,172102152,1264512413,70831408,169372389,1253168177,273323242,1333646232,883433682,2147305130,662141325,702210019]
def s22 : Fin 16 → M := ![1299612607,1015453301,1701372696,197691349,1571161805,1738599499,942949364,1074448450,1382142571,230806035,220620301,975146107,898886583,187307658,1691727701,158361661]
def s23 : Fin 16 → M := ![782654342,937915787,1712321222,2116602281,1407017630,1177878323,1825454929,2010056932,1979600259,1507307602,1383497625,725849734,1973858723,893613922,296232942,1953467810]
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
def left : Fin 8 → M := ![1197839198,449684346,391417085,13476115,411598282,1584375671,1644734677,28127165]
def right : Fin 8 → M := ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885]
def output : Fin 8 → M := ![782654342,937915787,1712321222,2116602281,1407017630,1177878323,1825454929,2010056932]
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
end AspisR1.PV_2TNV_Node10
