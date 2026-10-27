import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_9_0 : Fin 16 → Scalar := ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718,27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,1649667347]
def s_9_1 : Fin 16 → Scalar := ![1483569129,699753261,758907557,1759174763,1963719024,119428538,717775996,182281879,1483569129,699753261,758907557,1759174763,912198006,1215391167,1858180236,226723490]
theorem round_9_1 : poseidonExternalLinear s_9_0 = s_9_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_1
def s_9_2 : Fin 16 → Scalar := ![1480128484,190545093,690317591,913105803,447018792,608806021,554119116,564548330,899821541,1743587724,910100036,1081823136,184942177,2093581159,466924549,452364162]
theorem round_9_2 : poseidonFullRound s_9_1 (poseidonExternalInitial 0) = s_9_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_2
def s_9_3 : Fin 16 → Scalar := ![1545743412,1259592318,73989651,878854208,457860518,1043713056,220558167,120943054,1687739412,2054467403,1422063297,274888616,1171908488,2042077783,2112134600,279883104]
theorem round_9_3 : poseidonFullRound s_9_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_9_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_3
def s_9_4 : Fin 16 → Scalar := ![1292679804,1245392486,1546816234,1630900839,1286207907,576183033,1410086609,2790043,1782780429,1472904177,603381427,1198447119,1816618592,1866458362,2134577258,370352724]
theorem round_9_4 : poseidonFullRound s_9_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_9_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_4
def s_9_5 : Fin 16 → Scalar := ![2012701793,1761845043,2036658470,29551000,1561017281,567161304,1587512933,893527835,550325666,941081991,503682568,1009113719,1269059563,1683925420,435815753,1781304996]
theorem round_9_5 : poseidonFullRound s_9_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_9_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_5
def s_9_6 : Fin 16 → Scalar := ![2141968708,630788714,794776964,1134631318,619663684,1501073594,277233646,220150289,591152215,1415248550,1391301670,440199867,1184032287,1728095589,1060769072,1262110607]
theorem round_9_6 : poseidonInternalRound s_9_5 (poseidonInternalConstants 0) = s_9_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_6
def s_9_7 : Fin 16 → Scalar := ![1905633720,1457807362,269088929,1070576626,1489360826,1221876035,1108560732,2031735262,1332574523,205911105,1738270767,2146894047,235880253,1520746776,937659602,2027611148]
theorem round_9_7 : poseidonInternalRound s_9_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_9_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_7
def s_9_8 : Fin 16 → Scalar := ![1442034018,1097659331,178029827,1774674826,817320342,2009999353,754057041,821889917,558182800,813487321,1512657661,1519817663,1383085892,449757459,821152676,1318421878]
theorem round_9_8 : poseidonInternalRound s_9_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_9_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_8
def s_9_9 : Fin 16 → Scalar := ![68658313,477134287,1883018257,35723319,1623070398,1474693546,2034463798,440822116,2107396652,1473799020,5210333,1145013598,1642864295,189290355,1087748861,1618618166]
theorem round_9_9 : poseidonInternalRound s_9_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_9_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_9
def s_9_10 : Fin 16 → Scalar := ![450951299,144178638,1285597218,1957421274,1914189300,1787304617,345376477,2109856011,978359932,1149955246,707458049,1685940358,1878816889,33834403,1235632340,324944115]
theorem round_9_10 : poseidonInternalRound s_9_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_9_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_10
def s_9_11 : Fin 16 → Scalar := ![1892007992,1117645675,1397177826,213217545,1254595908,1653053498,1288096066,712781980,1649486807,1156750374,1708520174,277764653,1226123676,1265544863,1517303619,2063144025]
theorem round_9_11 : poseidonInternalRound s_9_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_9_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_11
def s_9_12 : Fin 16 → Scalar := ![1273026663,339810391,2016520368,75034896,668997392,2048700567,1786533182,1890538496,2050562253,1145000821,695134234,927334141,1993785136,2102071970,1833240411,1711088349]
theorem round_9_12 : poseidonInternalRound s_9_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_9_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_12
def s_9_13 : Fin 16 → Scalar := ![1508379139,597947173,2143693871,558276366,1315148624,825091149,1592623784,993516294,737100232,1320570966,1258505241,1867690422,1732835459,1410046323,319866899,843097800]
theorem round_9_13 : poseidonInternalRound s_9_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_9_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_13
def s_9_14 : Fin 16 → Scalar := ![1100757574,169472453,1711429375,1804630744,1502779684,2035565429,1143362487,879542333,1578558155,482759997,1938187511,294743178,92698738,1288890533,1249874352,222192417]
theorem round_9_14 : poseidonInternalRound s_9_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_9_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_14
def s_9_15 : Fin 16 → Scalar := ![1279391599,1614684568,573103571,73800503,582547705,1802004274,1525589700,1901346605,1637193137,477719821,1874333551,1827459589,624062773,273520189,519862867,960842320]
theorem round_9_15 : poseidonInternalRound s_9_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_9_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_15
def s_9_16 : Fin 16 → Scalar := ![145351446,1793220763,1324743337,473738207,543950541,1093317168,1752766361,1605634683,1433343972,68242492,1793195648,1472502944,1489692751,1882425129,1204674047,1425322381]
theorem round_9_16 : poseidonInternalRound s_9_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_9_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_16
def s_9_17 : Fin 16 → Scalar := ![909933384,942122581,1798388492,1043854646,1353022499,1609590977,1550334195,977790121,80820239,1586594241,1430210832,386879666,709835756,789560787,1011158407,2127753122]
theorem round_9_17 : poseidonInternalRound s_9_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_9_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_17
def s_9_18 : Fin 16 → Scalar := ![1055867671,322349680,829520436,1408162036,1614472503,1511362614,1746281105,1829252727,1135283103,1821427159,1479755460,1343891196,1116507822,1250155426,1641201759,1253179840]
theorem round_9_18 : poseidonInternalRound s_9_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_9_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_18
def s_9_19 : Fin 16 → Scalar := ![1736236917,537012849,1873704041,1552344019,245541311,774144876,261083707,1322720759,1649496004,496064474,1508283074,792414724,513888420,62137667,1828413907,244061541]
theorem round_9_19 : poseidonInternalRound s_9_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_9_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_19
def s_9_20 : Fin 16 → Scalar := ![163009752,1570634618,24002255,978177271,1146434436,272448145,85296060,851623245,448831529,921537560,1508621165,2127349129,743295819,1941874936,722828769,2096920421]
theorem round_9_20 : poseidonFullRound s_9_19 (poseidonExternalFinal 0) = s_9_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_20
def s_9_21 : Fin 16 → Scalar := ![1680113396,2021296075,74185460,775796973,1705151962,1958216511,738490454,1872467762,1616920282,894020622,397274675,280678031,47357483,1029262297,1179923466,429642641]
theorem round_9_21 : poseidonFullRound s_9_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_9_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_21
def s_9_22 : Fin 16 → Scalar := ![912370333,506443592,400946600,1798023497,1660140552,1113592478,1786092199,1344576227,597333048,97853046,317095784,1732669182,1503459274,1348604195,126652404,487434064]
theorem round_9_22 : poseidonFullRound s_9_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_9_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_22
def s_9_23 : Fin 16 → Scalar := ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885,1374480701,671490677,1299580993,143232035,2144020410,1928967176,526689528,613595874]
theorem round_9_23 : poseidonFullRound s_9_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_9_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_9_23
theorem permutation_9 : poseidonPermutation s_9_0 = s_9_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_9_1,round_9_2,round_9_3,round_9_4,round_9_5,round_9_6,round_9_7,round_9_8,round_9_9,round_9_10,round_9_11,round_9_12,round_9_13,round_9_14,round_9_15,round_9_16,round_9_17,round_9_18,round_9_19,round_9_20,round_9_21,round_9_22,round_9_23]
#print axioms permutation_9
theorem parent_9 : nodeCompress (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] = ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_9_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_9]
  funext i
  fin_cases i <;> rfl
#print axioms parent_9
end R1Z.PV_RunJoin_RootModel
