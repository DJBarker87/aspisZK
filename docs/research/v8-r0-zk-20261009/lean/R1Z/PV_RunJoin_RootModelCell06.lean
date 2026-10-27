import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_6_0 : Fin 16 → Scalar := ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592,1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,1657047221]
def s_6_1 : Fin 16 → Scalar := ![1307663887,2140306168,132048541,2028966059,173934438,419598905,125398208,1326872656,1307663887,2140306168,132048541,2028966059,1269897067,1515561534,1265802448,1371314267]
theorem round_6_1 : poseidonExternalLinear s_6_0 = s_6_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_1
def s_6_2 : Fin 16 → Scalar := ![1354042277,2006618528,2031860171,195723157,801869547,1719050748,720076358,2110775971,953907932,1204762521,1631029075,297446570,917388388,1663607714,140374858,380192431]
theorem round_6_2 : poseidonFullRound s_6_1 (poseidonExternalInitial 0) = s_6_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_2
def s_6_3 : Fin 16 → Scalar := ![551022301,440911999,1328777279,1436773789,442243623,1861800356,1023258030,226061562,1961489701,610307760,1255819461,544359490,113188061,1765022452,73667331,1290734725]
theorem round_6_3 : poseidonFullRound s_6_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_6_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_3
def s_6_4 : Fin 16 → Scalar := ![530523982,512236816,116355583,605710182,1612265202,1378914033,575779688,494931781,1186636684,2119500254,1991662086,742096569,1878399001,547278402,2131992781,930127139]
theorem round_6_4 : poseidonFullRound s_6_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_6_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_4
def s_6_5 : Fin 16 → Scalar := ![512358414,2076999835,178106604,1292119599,907415598,278587492,1686389647,69630211,497675205,1059770482,1507430386,930611933,423192124,442672938,1864260743,1977579770]
theorem round_6_5 : poseidonFullRound s_6_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_6_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_5
def s_6_6 : Fin 16 → Scalar := ![1928456539,468657372,895354392,1412652286,1356015027,701573762,816518713,700507394,1964541661,1257445054,107114255,542145327,1290414734,1240281457,1315345246,421367807]
theorem round_6_6 : poseidonInternalRound s_6_5 (poseidonInternalConstants 0) = s_6_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_6
def s_6_7 : Fin 16 → Scalar := ![1120537731,410701204,1732752616,1297685682,52745813,429805789,300838884,1824844108,147789741,1872914253,105374955,71212226,1105034226,1223167406,1178269470,210426611]
theorem round_6_7 : poseidonInternalRound s_6_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_6_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_7
def s_6_8 : Fin 16 → Scalar := ![1756541096,1106449606,2013769987,1591523836,1117714906,1130190085,1732658102,1521654376,285482427,1272943889,1225519972,323250106,1492555689,753134502,621251949,74145864]
theorem round_6_8 : poseidonInternalRound s_6_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_6_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_8
def s_6_9 : Fin 16 → Scalar := ![1458448041,2107721099,733844173,924915896,1353056153,1904443677,611755935,1750387442,1035800150,457392733,1803272973,36295470,245589763,915916599,40162765,469121436]
theorem round_6_9 : poseidonInternalRound s_6_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_6_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_9
def s_6_10 : Fin 16 → Scalar := ![1435643176,1534143040,894110287,978601878,1660936577,1980233362,1822742685,1929552232,1012338674,554844651,1289493520,2063779065,1253066845,1335738368,1219913497,392961185]
theorem round_6_10 : poseidonInternalRound s_6_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_6_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_10
def s_6_11 : Fin 16 → Scalar := ![903052605,1821296521,2075374055,2054077346,689744215,1906116215,632860932,1371928450,1017484933,593463435,26075056,1030569129,438915061,18728216,1152017919,767478817]
theorem round_6_11 : poseidonInternalRound s_6_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_6_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_11
def s_6_12 : Fin 16 → Scalar := ![545615705,255686711,437654653,208248633,1804860263,1014962219,1506070838,338465110,1970926441,37174260,1512927417,1987659866,1286428471,334803260,1437496663,1859128362]
theorem round_6_12 : poseidonInternalRound s_6_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_6_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_12
def s_6_13 : Fin 16 → Scalar := ![451486149,1724415838,196554786,154240012,875225702,528255455,270872062,1655659697,344243229,247921452,223211001,1813034486,41024083,64622882,305585366,1672864967]
theorem round_6_13 : poseidonInternalRound s_6_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_6_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_13
def s_6_14 : Fin 16 → Scalar := ![177069480,307971924,1124149305,1347999781,1290394408,593192425,809011129,1466561638,1844500105,1921905682,1665838175,921843063,1792878737,802900450,436066860,274370401]
theorem round_6_14 : poseidonInternalRound s_6_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_6_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_14
def s_6_15 : Fin 16 → Scalar := ![797155983,497729402,290572441,1286789308,1922978154,1090901690,308309842,1707905489,62569748,423856907,906032960,782692100,811709149,1573392403,2019922467,447781083]
theorem round_6_15 : poseidonInternalRound s_6_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_6_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_15
def s_6_16 : Fin 16 → Scalar := ![1764812933,1229398991,1312814471,1583859527,1083109292,1006227453,2007649945,515954888,150662745,1864855431,796485125,445426218,1643647085,799101753,1957584058,1148688822]
theorem round_6_16 : poseidonInternalRound s_6_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_6_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_16
def s_6_17 : Fin 16 → Scalar := ![299354382,1661237865,909984169,324826041,506778622,1499092593,252127704,1240697001,389317411,1093459576,2136304661,1684011499,466292504,1854647914,1209715528,863231881]
theorem round_6_17 : poseidonInternalRound s_6_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_6_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_17
def s_6_18 : Fin 16 → Scalar := ![1943521042,1836395703,1995126176,1474462002,2081903167,538319209,1800793425,122870963,615662565,927935184,1612778056,168783578,1817426240,1980459411,1880423016,1777998133]
theorem round_6_18 : poseidonInternalRound s_6_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_6_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_18
def s_6_19 : Fin 16 → Scalar := ![958637547,1338242519,1344615521,1104727530,1124686623,1672503219,1292661594,923137507,997243844,830052750,1719135264,1497131617,1500963892,1018414117,1602435380,2072288531]
theorem round_6_19 : poseidonInternalRound s_6_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_6_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_19
def s_6_20 : Fin 16 → Scalar := ![980905388,478070008,1558445799,555036293,676744742,255035885,1417253172,851006832,122712913,787517917,1770816992,1625902064,530310209,608721330,1174203139,1577953280]
theorem round_6_20 : poseidonFullRound s_6_19 (poseidonExternalFinal 0) = s_6_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_20
def s_6_21 : Fin 16 → Scalar := ![620200288,82065962,1506959708,1636215156,1385017963,159578556,1690027010,1750540431,371394959,1302113836,806216097,988443943,1898378901,1576575038,810436834,763297404]
theorem round_6_21 : poseidonFullRound s_6_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_6_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_21
def s_6_22 : Fin 16 → Scalar := ![1387828472,1407794201,721455142,782147538,938311726,1500254538,184901247,1044387406,1755671188,611679005,1524301423,1427226470,1884923343,1343914519,1158301410,1636667962]
theorem round_6_22 : poseidonFullRound s_6_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_6_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_22
def s_6_23 : Fin 16 → Scalar := ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587,1078964711,1845225832,2060143703,1700404629,301692887,1648740357,898677664,335812516]
theorem round_6_23 : poseidonFullRound s_6_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_6_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_23
theorem permutation_6 : poseidonPermutation s_6_0 = s_6_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_6_1,round_6_2,round_6_3,round_6_4,round_6_5,round_6_6,round_6_7,round_6_8,round_6_9,round_6_10,round_6_11,round_6_12,round_6_13,round_6_14,round_6_15,round_6_16,round_6_17,round_6_18,round_6_19,round_6_20,round_6_21,round_6_22,round_6_23]
#print axioms permutation_6
theorem parent_6 : nodeCompress (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] = ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_6_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_6]
  funext i
  fin_cases i <;> rfl
#print axioms parent_6
end R1Z.PV_RunJoin_RootModel
