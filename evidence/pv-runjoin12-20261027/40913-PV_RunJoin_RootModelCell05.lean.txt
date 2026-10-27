import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_5_0 : Fin 16 → Scalar := ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616,1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,803983598]
def s_5_1 : Fin 16 → Scalar := ![1749134129,1578107267,2059409860,2096399335,1966602533,1141647589,211309014,23672399,1749134129,1578107267,2059409860,2096399335,915081515,90126571,1351713254,68114010]
theorem round_5_1 : poseidonExternalLinear s_5_0 = s_5_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_1
def s_5_2 : Fin 16 → Scalar := ![2065286669,897533768,48886656,198271263,900503075,1768159249,543857096,1603583514,751900425,107422375,1611725300,150326059,233315006,1749892453,758830500,707678771]
theorem round_5_2 : poseidonFullRound s_5_1 (poseidonExternalInitial 0) = s_5_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_2
def s_5_3 : Fin 16 → Scalar := ![1138253420,1537472255,896476377,1838850017,778600736,5785602,871968606,454039221,1258459819,121904277,1533135756,635026075,583079191,1066141688,438142403,907097042]
theorem round_5_3 : poseidonFullRound s_5_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_5_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_3
def s_5_4 : Fin 16 → Scalar := ![956879271,1494646892,452113902,1582372303,1719963679,140499407,760236682,423528280,377600845,348911856,1354345718,938948611,1681856580,417638653,224286955,1946656815]
theorem round_5_4 : poseidonFullRound s_5_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_5_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_4
def s_5_5 : Fin 16 → Scalar := ![1312738641,220147285,1122920602,1487797585,1081605920,1730350537,1495683307,1473009694,2105298345,533533708,453484509,1224515961,1381530164,806516148,612523683,2103127407]
theorem round_5_5 : poseidonFullRound s_5_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_5_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_5
def s_5_6 : Fin 16 → Scalar := ![898535512,625963131,504173403,2062038892,468728618,174137027,1023041436,189155794,1448548131,1698975333,917485310,1648876357,662099644,899504687,1199695528,1168129244]
theorem round_5_6 : poseidonInternalRound s_5_5 (poseidonInternalConstants 0) = s_5_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_6
def s_5_7 : Fin 16 → Scalar := ![2094880044,2142384393,377284421,1174642242,971282912,7646400,2041492509,737490196,99504741,514926169,423541316,1477909719,893012588,820943709,1303840784,390024143]
theorem round_5_7 : poseidonInternalRound s_5_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_5_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_7
def s_5_8 : Fin 16 → Scalar := ![1587506938,1536926175,149110624,1945627103,722354137,1664367829,297792660,1496757739,1393730395,219138579,1456636319,1303833560,624360996,46188877,1609678476,666410836]
theorem round_5_8 : poseidonInternalRound s_5_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_5_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_8
def s_5_9 : Fin 16 → Scalar := ![610827782,1127155945,2035934665,930287241,1074095572,450311270,529660302,893444598,1894061276,2002614819,832169408,1448145088,1196945495,434546794,1188677371,115848827]
theorem round_5_9 : poseidonInternalRound s_5_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_5_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_9
def s_5_10 : Fin 16 → Scalar := ![1049871452,172827130,970056868,619336502,1195984820,1955684211,962415320,391550635,967346049,613956863,783620765,1445602266,1160317670,1899537923,714858474,2107188959]
theorem round_5_10 : poseidonInternalRound s_5_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_5_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_10
def s_5_11 : Fin 16 → Scalar := ![630749560,1397875422,1017678381,1554910653,55508617,303740963,1957567474,514485168,491291038,1631698989,493827674,1799515049,1784779310,1921366400,955902848,1877261334]
theorem round_5_11 : poseidonInternalRound s_5_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_5_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_11
def s_5_12 : Fin 16 → Scalar := ![531733081,2021222629,511220322,400538878,1067416143,1188235321,988480612,1338143254,1231574308,1726460873,1644228338,1273111407,1466785951,327663434,451395329,1631479248]
theorem round_5_12 : poseidonInternalRound s_5_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_5_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_12
def s_5_13 : Fin 16 → Scalar := ![1271603587,925792784,2074494446,506725667,1001448358,736466115,471178681,793876178,1927258995,644406008,1114692666,1626081958,1791559429,780638958,506833938,612750247]
theorem round_5_13 : poseidonInternalRound s_5_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_5_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_13
def s_5_14 : Fin 16 → Scalar := ![275161601,1614268981,542497795,567895218,110128473,1734515802,733808460,2104427708,417008152,300173426,1819949624,1773386818,1240074967,264562537,2131914330,2091948336]
theorem round_5_14 : poseidonInternalRound s_5_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_5_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_14
def s_5_15 : Fin 16 → Scalar := ![1952372128,195279755,1813490011,852591646,1609522205,563459842,588045024,120397972,418446702,263480185,341103801,1731206795,1824973775,1699100983,1654222951,1151134390]
theorem round_5_15 : poseidonInternalRound s_5_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_5_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_15
def s_5_16 : Fin 16 → Scalar := ![1571198642,359705776,1643922396,1427308958,155701779,589848905,1801997613,1427445288,38512702,1043360324,1562367431,196455947,1715924054,404415432,1107350462,1954773598]
theorem round_5_16 : poseidonInternalRound s_5_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_5_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_16
def s_5_17 : Fin 16 → Scalar := ![1307501269,1993098426,626270148,900177541,731523235,333556895,1315257797,648094261,120567565,298179719,1622324979,1010583937,1055289756,441295896,1262148107,1538949393]
theorem round_5_17 : poseidonInternalRound s_5_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_5_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_17
def s_5_18 : Fin 16 → Scalar := ![1214292914,656153411,2063078928,116281502,220273571,1852481658,2096598843,1486382043,1210801423,1982619051,2066457997,1961356815,2122540609,425059247,492151235,828476925]
theorem round_5_18 : poseidonInternalRound s_5_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_5_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_18
def s_5_19 : Fin 16 → Scalar := ![1292010340,2018347588,1193384739,1827320185,976899098,937129647,1881364096,2001364461,1725953737,2106530541,2143790810,1343384990,1039773346,1243429804,571673687,1596903876]
theorem round_5_19 : poseidonInternalRound s_5_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_5_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_19
def s_5_20 : Fin 16 → Scalar := ![399200905,2056123400,1294465334,2066058024,2117031063,253500960,298945330,1809500461,2127800831,1207878979,2115838388,930478340,751612337,179434044,416122236,1859638561]
theorem round_5_20 : poseidonFullRound s_5_19 (poseidonExternalFinal 0) = s_5_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_20
def s_5_21 : Fin 16 → Scalar := ![1654002825,2041028188,115771673,2008589431,333009724,1585259147,411546798,1817304077,22691728,1134935415,1440245219,698945559,282485580,1493108836,17276432,49818396]
theorem round_5_21 : poseidonFullRound s_5_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_5_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_21
def s_5_22 : Fin 16 → Scalar := ![357132502,1541422002,744695866,1478374548,702487860,1054892008,985938284,203125596,1921898624,409317712,953274009,1105790991,117588151,717618386,620212806,841041798]
theorem round_5_22 : poseidonFullRound s_5_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_5_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_22
def s_5_23 : Fin 16 → Scalar := ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592,349150998,528175160,651700178,100615271,870008081,2137431373,1868237087,1382315420]
theorem round_5_23 : poseidonFullRound s_5_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_5_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_5_23
theorem permutation_5 : poseidonPermutation s_5_0 = s_5_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_5_1,round_5_2,round_5_3,round_5_4,round_5_5,round_5_6,round_5_7,round_5_8,round_5_9,round_5_10,round_5_11,round_5_12,round_5_13,round_5_14,round_5_15,round_5_16,round_5_17,round_5_18,round_5_19,round_5_20,round_5_21,round_5_22,round_5_23]
#print axioms permutation_5
theorem parent_5 : nodeCompress (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] = ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_5_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_5]
  funext i
  fin_cases i <;> rfl
#print axioms parent_5
end R1Z.PV_RunJoin_RootModel
