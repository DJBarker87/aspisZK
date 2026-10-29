import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_7_0 : Fin 16 → Scalar := ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587,244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,1841894216]
def s_7_1 : Fin 16 → Scalar := ![729913844,1737702116,1883619271,516066678,1369369006,761333841,2139365713,726738331,729913844,1737702116,1883619271,516066678,317847988,1857296470,1132286306,771179942]
theorem round_7_1 : poseidonExternalLinear s_7_0 = s_7_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_1
def s_7_2 : Fin 16 → Scalar := ![741614129,1380622704,1773584610,1138734495,706567458,96182132,1696439526,1887127605,1270019093,1605958558,1749587762,459994678,1189012808,719124477,2035623650,107898892]
theorem round_7_2 : poseidonFullRound s_7_1 (poseidonExternalInitial 0) = s_7_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_2
def s_7_3 : Fin 16 → Scalar := ![743122424,907559949,1570657332,2142481714,1147015305,338532686,1724201019,558962822,905736437,1467212287,1734660176,1275061500,463618627,29274064,1505263430,751501655]
theorem round_7_3 : poseidonFullRound s_7_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_7_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_3
def s_7_4 : Fin 16 → Scalar := ![1659813431,958263456,1517926172,27739392,361459005,1666890712,152444271,1885943807,340918347,233972021,357757662,2079379914,1813860840,695694415,783834211,830313577]
theorem round_7_4 : poseidonFullRound s_7_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_7_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_4
def s_7_5 : Fin 16 → Scalar := ![1776850124,1832202070,195421076,1540064688,941575092,1650382068,19324131,146702222,942442905,1651327697,281838382,1467317943,1778520982,1167576855,610596558,1163786900]
theorem round_7_5 : poseidonFullRound s_7_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_7_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_5
def s_7_6 : Fin 16 → Scalar := ![407551105,2138039045,696679127,23644786,1395986770,942146299,924209167,1104844595,679444583,2138932595,1145531445,1780887197,1420660271,100701819,228710420,214908523]
theorem round_7_6 : poseidonInternalRound s_7_5 (poseidonInternalConstants 0) = s_7_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_6
def s_7_7 : Fin 16 → Scalar := ![1415365916,528555355,1931358211,632579101,968475882,579955212,47922243,381093686,1607560701,496414292,1036128375,50010010,1373056896,1169161557,203114487,1585206259]
theorem round_7_7 : poseidonInternalRound s_7_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_7_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_7
def s_7_8 : Fin 16 → Scalar := ![909696752,1177723020,216916793,1032000422,1954523780,1338516469,35195794,1416843452,258507281,1029691244,787702047,1479222160,211916711,637986313,1252855628,2057650217]
theorem round_7_8 : poseidonInternalRound s_7_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_7_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_8
def s_7_9 : Fin 16 → Scalar := ![819060843,68393781,1471987994,871188802,1641959119,979581442,16936169,1521822162,1914831671,498624291,191199264,1880753581,1893064144,2002996651,1166493013,2114646002]
theorem round_7_9 : poseidonInternalRound s_7_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_7_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_9
def s_7_10 : Fin 16 → Scalar := ![1779880231,397731370,1125829930,1666609150,580108659,970255132,871294997,1089191842,614655719,1275620912,696372048,872163576,1331390250,1728857766,910954620,60049163]
theorem round_7_10 : poseidonInternalRound s_7_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_7_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_10
def s_7_11 : Fin 16 → Scalar := ![1764682606,1245415268,951860111,1071669557,1193585876,1339380481,811836391,1836485082,66720991,989123026,968090246,1964386233,527168785,1144018112,985978758,2039588962]
theorem round_7_11 : poseidonInternalRound s_7_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_7_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_11
def s_7_12 : Fin 16 → Scalar := ![1011370176,144922498,803227452,1038701811,2005743297,1002242103,1255951625,470435540,997343137,859415187,233957867,551775936,1024063480,1402466869,707463906,1724564288]
theorem round_7_12 : poseidonInternalRound s_7_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_7_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_12
def s_7_13 : Fin 16 → Scalar := ![480138660,192046419,1653578825,2054447518,1060684768,1050612040,1582870275,90227423,1005510284,1014079799,1249294912,968561133,1104026899,2136766364,138426364,1175444326]
theorem round_7_13 : poseidonInternalRound s_7_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_7_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_13
def s_7_14 : Fin 16 → Scalar := ![1164953722,1915476337,735620274,1351285402,1618973474,1353353382,835671190,1055534049,1579727450,1482337175,1101166194,400051030,710665362,77640653,45579359,1109393470]
theorem round_7_14 : poseidonInternalRound s_7_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_7_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_14
def s_7_15 : Fin 16 → Scalar := ![713515872,1882139009,1437903220,1076836986,33548582,145480314,938336988,948848751,308313454,1487857600,131930653,45658891,2056624806,720802400,1009963719,2118243407]
theorem round_7_15 : poseidonInternalRound s_7_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_7_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_15
def s_7_16 : Fin 16 → Scalar := ![712296936,1937532222,783716006,67773863,323781869,235594590,17405771,652171161,864809679,842333294,2008395771,243133460,916593250,669339960,1823537135,1469921344]
theorem round_7_16 : poseidonInternalRound s_7_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_7_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_16
def s_7_17 : Fin 16 → Scalar := ![456785669,1423021539,1052921329,1904068416,2075744269,1107519110,42473989,422254328,659462232,374447881,940908642,1075212916,614563405,899892375,1565334869,429252575]
theorem round_7_17 : poseidonInternalRound s_7_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_7_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_17
def s_7_18 : Fin 16 → Scalar := ![1453675037,1226214841,1909035960,977016025,1376761925,343629886,1162360950,1057666530,462496765,1172570370,1220968854,1533820888,604938494,1164628647,49272099,1411656449]
theorem round_7_18 : poseidonInternalRound s_7_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_7_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_18
def s_7_19 : Fin 16 → Scalar := ![1923151624,584369525,1028742957,1118735137,1782315496,561265566,46483085,476819547,575682135,1035942471,1942262273,498844457,769523903,241703537,1146075819,79683588]
theorem round_7_19 : poseidonInternalRound s_7_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_7_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_19
def s_7_20 : Fin 16 → Scalar := ![1654500173,1761377206,2002925315,1334358819,682769271,478696551,382557603,1215566095,333919232,2062609536,190754231,1147555658,960345264,2143228971,1204842789,1479574224]
theorem round_7_20 : poseidonFullRound s_7_19 (poseidonExternalFinal 0) = s_7_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_20
def s_7_21 : Fin 16 → Scalar := ![903099318,1028889951,1744444121,980211600,1537360521,1903922427,859181720,208118190,542007394,826868650,317875305,826486329,913270906,990238071,506198896,36745938]
theorem round_7_21 : poseidonFullRound s_7_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_7_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_21
def s_7_22 : Fin 16 → Scalar := ![2032431166,1802123003,195858163,1472671520,326983066,859456492,1706982008,858604295,444440136,785069964,659366088,2145789844,1354532417,516462657,1112960697,1283699710]
theorem round_7_22 : poseidonFullRound s_7_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_7_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_22
def s_7_23 : Fin 16 → Scalar := ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631,981161077,1435260996,1118356433,2084833331,2041323855,148461776,81005948,95315013]
theorem round_7_23 : poseidonFullRound s_7_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_7_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_23
theorem permutation_7 : poseidonPermutation s_7_0 = s_7_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_7_1,round_7_2,round_7_3,round_7_4,round_7_5,round_7_6,round_7_7,round_7_8,round_7_9,round_7_10,round_7_11,round_7_12,round_7_13,round_7_14,round_7_15,round_7_16,round_7_17,round_7_18,round_7_19,round_7_20,round_7_21,round_7_22,round_7_23]
#print axioms permutation_7
theorem parent_7 : nodeCompress (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] = ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_7_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_7]
  funext i
  fin_cases i <;> rfl
#print axioms parent_7
end R1Z.PV_RunJoin_RootModel
