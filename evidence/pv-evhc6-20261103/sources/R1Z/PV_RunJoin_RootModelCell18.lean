import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_18_0 : Fin 16 → Scalar := ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413,1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,248459395]
def s_18_1 : Fin 16 → Scalar := ![1125509804,677241713,415969725,279166115,1042710609,1773184708,1114268463,1795515498,1125509804,677241713,415969725,279166115,2138673238,721663690,107189056,1839957109]
theorem round_18_1 : poseidonExternalLinear s_18_0 = s_18_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_1
def s_18_2 : Fin 16 → Scalar := ![66376626,791704627,1272204145,644061664,401376784,1090662898,291478337,1905268974,819923953,1314259697,436729616,360410952,1645257663,379366700,502841061,318898252]
theorem round_18_2 : poseidonFullRound s_18_1 (poseidonExternalInitial 0) = s_18_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_2
def s_18_3 : Fin 16 → Scalar := ![2096898629,1191200282,884576646,976077927,411658220,1170713383,1320867534,1054310965,855111459,1981140416,819884220,922373543,2063502581,2108008270,535850982,731584957]
theorem round_18_3 : poseidonFullRound s_18_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_18_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_3
def s_18_4 : Fin 16 → Scalar := ![1130249439,329565542,750936947,1670947470,1082688478,1812867893,298065389,103615106,1105629336,840664809,375179664,283922755,1014709357,1905270711,1329493875,768052220]
theorem round_18_4 : poseidonFullRound s_18_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_18_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_4
def s_18_5 : Fin 16 → Scalar := ![1599563515,1882464591,1786745698,579994946,1656335355,1098473471,1551499647,1974074124,485641448,1441007649,758055424,709058072,1968500196,232229418,238076395,1567053188]
theorem round_18_5 : poseidonFullRound s_18_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_18_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_5
def s_18_6 : Fin 16 → Scalar := ![898983803,334678033,2025704838,772193226,965478047,995403449,855561912,238905852,484776670,130467949,1606854698,1503669257,1098597398,105459117,78918898,2034459023]
theorem round_18_6 : poseidonInternalRound s_18_5 (poseidonInternalConstants 0) = s_18_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_6
def s_18_7 : Fin 16 → Scalar := ![1089890827,2084723823,1506488172,543851400,883935578,496631798,1210739563,2007634789,1524433787,790102382,49299293,1796222866,1355965629,867882883,46700819,1239385829]
theorem round_18_7 : poseidonInternalRound s_18_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_18_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_7
def s_18_8 : Fin 16 → Scalar := ![160712195,372270498,1300523019,462952275,1064064005,1938688149,523990692,74637998,141543181,837777296,1525382473,484914836,1720040806,1338958607,1719110650,550739185]
theorem round_18_8 : poseidonInternalRound s_18_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_18_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_8
def s_18_9 : Fin 16 → Scalar := ![1177990698,1535663376,1616955269,867718331,1085970330,2117632204,751225846,1645257456,2101050870,886015954,1934433861,952187659,2097467663,2115755861,190143974,1648965909]
theorem round_18_9 : poseidonInternalRound s_18_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_18_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_9
def s_18_10 : Fin 16 → Scalar := ![238844030,1440035532,990799047,1227761833,2200208,1574232715,321279111,2121634284,403427641,1238673445,784723286,234720468,342807805,1914852553,692052241,862100046]
theorem round_18_10 : poseidonInternalRound s_18_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_18_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_10
def s_18_11 : Fin 16 → Scalar := ![1818162987,7185564,548748126,1330713717,732235343,132553355,258146996,1207758094,813764199,2134939490,1112394565,56996751,87561963,1070263008,455154447,1155979412]
theorem round_18_11 : poseidonInternalRound s_18_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_18_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_11
def s_18_12 : Fin 16 → Scalar := ![1382167957,1506454844,449281885,379673207,914701083,1472639313,1170038564,1486376004,434388049,435448735,277487283,882243853,1547332078,336930950,1726260161,837915246]
theorem round_18_12 : poseidonInternalRound s_18_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_18_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_12
def s_18_13 : Fin 16 → Scalar := ![1886771917,1564221673,956330599,1576459657,932924552,2145159367,991778878,696550617,1972345926,2010976992,736903217,1661094463,1353665211,1301478839,1431460497,366991248]
theorem round_18_13 : poseidonInternalRound s_18_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_18_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_13
def s_18_14 : Fin 16 → Scalar := ![1771202254,534997245,883436770,981646906,2139204694,1081070739,642928610,600342120,175467401,532293891,1940393330,1732985971,738114623,34942685,1878007141,439841747]
theorem round_18_14 : poseidonInternalRound s_18_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_18_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_14
def s_18_15 : Fin 16 → Scalar := ![1359554701,2076986526,1161379174,1173609611,1475757657,1659251929,640868331,1309179315,379496492,370271969,2082385726,271589515,863030945,664806572,1788597137,1337726992]
theorem round_18_15 : poseidonInternalRound s_18_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_18_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_15
def s_18_16 : Fin 16 → Scalar := ![492600598,1734523358,1980295180,57007982,726179853,435763932,837970601,1840634406,988447574,2105364075,1716742432,1839144773,90872348,1958838543,1432311771,61279416]
theorem round_18_16 : poseidonInternalRound s_18_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_18_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_16
def s_18_17 : Fin 16 → Scalar := ![106860246,731193601,809776956,1372185818,511141773,1673925861,41925711,833155289,963908189,1098961693,299297365,908510422,393603197,611737987,1881160833,1357540976]
theorem round_18_17 : poseidonInternalRound s_18_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_18_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_17
def s_18_18 : Fin 16 → Scalar := ![349496772,1587944407,328821071,2050526784,650917696,1869760818,50889911,491598127,1830431119,870586457,247091045,526279067,1881186483,1265749265,1364323062,562142379]
theorem round_18_18 : poseidonInternalRound s_18_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_18_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_18
def s_18_19 : Fin 16 → Scalar := ![2139674700,539994031,1757175413,711705819,2011907545,950935301,580526776,349558694,1318998980,631366975,717693005,665010115,1436551135,885911952,923065641,1580519130]
theorem round_18_19 : poseidonInternalRound s_18_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_18_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_19
def s_18_20 : Fin 16 → Scalar := ![185332878,2065899042,1032392440,1355755789,1160204957,1751532235,778885183,1279301297,232605868,754819759,1994029038,772217663,1137216122,1715365875,1948651215,1685998701]
theorem round_18_20 : poseidonFullRound s_18_19 (poseidonExternalFinal 0) = s_18_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_20
def s_18_21 : Fin 16 → Scalar := ![1527527350,2125839917,883839716,1396509300,439371848,198046175,822325354,314705679,752895231,1839772805,1702998391,988714686,2021752358,1067847003,1073314476,1321111088]
theorem round_18_21 : poseidonFullRound s_18_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_18_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_21
def s_18_22 : Fin 16 → Scalar := ![286235914,578745453,417868910,1841742270,882779104,1115538826,1033848556,698796763,365126155,654409935,714551430,1002282150,325742861,831737828,545289922,1681734597]
theorem round_18_22 : poseidonFullRound s_18_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_18_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_22
def s_18_23 : Fin 16 → Scalar := ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803,1647797222,2070509097,761495651,757179561,1473957963,2088584511,498437579,1081393595]
theorem round_18_23 : poseidonFullRound s_18_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_18_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_23
theorem permutation_18 : poseidonPermutation s_18_0 = s_18_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_18_1,round_18_2,round_18_3,round_18_4,round_18_5,round_18_6,round_18_7,round_18_8,round_18_9,round_18_10,round_18_11,round_18_12,round_18_13,round_18_14,round_18_15,round_18_16,round_18_17,round_18_18,round_18_19,round_18_20,round_18_21,round_18_22,round_18_23]
#print axioms permutation_18
theorem parent_18 : nodeCompress (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] = ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_18_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_18]
  funext i
  fin_cases i <;> rfl
#print axioms parent_18
end R1Z.PV_RunJoin_RootModel
