import NDO_JFu_Q25InputBase
import NDO_JFu_FlatWindow
import NDO_JFr_EncodedCell
import NDO_JFu_DecodeAt
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def chunks : List (List U8) := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115]
theorem lengths : ∀ c ∈ chunks,c.length=32 := by
  intro c hc
  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82|h83|h84|h85|h86|h87|h88|h89|h90|h91|h92|h93|h94|h95|h96|h97|h98|h99|h100|h101|h102|h103|h104|h105|h106|h107|h108|h109|h110|h111|h112|h113|h114|h115
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
#print axioms lengths
def q000 : aspis_core.field.QM31 := ⟨⟨1262673698#u32,1732185580#u32⟩,⟨1505713530#u32,598598498#u32⟩⟩
def q001 : aspis_core.field.QM31 := ⟨⟨122159246#u32,1529111516#u32⟩,⟨1799434707#u32,1890743665#u32⟩⟩
def q002 : aspis_core.field.QM31 := ⟨⟨598058443#u32,361803088#u32⟩,⟨1483190859#u32,90368425#u32⟩⟩
def q003 : aspis_core.field.QM31 := ⟨⟨1592384557#u32,1945247415#u32⟩,⟨1778484467#u32,540792410#u32⟩⟩
def q004 : aspis_core.field.QM31 := ⟨⟨652624296#u32,575674261#u32⟩,⟨1739907054#u32,2128745497#u32⟩⟩
def q005 : aspis_core.field.QM31 := ⟨⟨261001302#u32,1433811342#u32⟩,⟨2093232551#u32,1795606717#u32⟩⟩
def q006 : aspis_core.field.QM31 := ⟨⟨1519785285#u32,417843121#u32⟩,⟨1706245526#u32,1595448726#u32⟩⟩
def q007 : aspis_core.field.QM31 := ⟨⟨844088711#u32,1816701484#u32⟩,⟨1695483190#u32,593217799#u32⟩⟩
def q008 : aspis_core.field.QM31 := ⟨⟨1758460621#u32,1711624258#u32⟩,⟨1933517417#u32,1591239394#u32⟩⟩
def q009 : aspis_core.field.QM31 := ⟨⟨1783465304#u32,2017546462#u32⟩,⟨1885178356#u32,269065480#u32⟩⟩
def q010 : aspis_core.field.QM31 := ⟨⟨1349681398#u32,213500445#u32⟩,⟨130549108#u32,1165426437#u32⟩⟩
def q011 : aspis_core.field.QM31 := ⟨⟨111471460#u32,2019486034#u32⟩,⟨196044068#u32,454889585#u32⟩⟩
def q012 : aspis_core.field.QM31 := ⟨⟨1389564877#u32,490792350#u32⟩,⟨498007426#u32,530169430#u32⟩⟩
def q013 : aspis_core.field.QM31 := ⟨⟨970136214#u32,353389341#u32⟩,⟨662936248#u32,1455264567#u32⟩⟩
def q014 : aspis_core.field.QM31 := ⟨⟨880136653#u32,1071546159#u32⟩,⟨1879016828#u32,1327520420#u32⟩⟩
def q015 : aspis_core.field.QM31 := ⟨⟨1928970014#u32,1690570642#u32⟩,⟨320451959#u32,1519481212#u32⟩⟩
def q016 : aspis_core.field.QM31 := ⟨⟨479557376#u32,317941656#u32⟩,⟨305958949#u32,1440737655#u32⟩⟩
def q017 : aspis_core.field.QM31 := ⟨⟨1156423977#u32,1883598252#u32⟩,⟨1752370157#u32,2077925937#u32⟩⟩
def q018 : aspis_core.field.QM31 := ⟨⟨382077289#u32,1383986122#u32⟩,⟨1094064853#u32,1092012613#u32⟩⟩
def q019 : aspis_core.field.QM31 := ⟨⟨156420109#u32,768169737#u32⟩,⟨457809055#u32,2121990699#u32⟩⟩
def q020 : aspis_core.field.QM31 := ⟨⟨1739440629#u32,614011834#u32⟩,⟨7009573#u32,1034581171#u32⟩⟩
def q021 : aspis_core.field.QM31 := ⟨⟨2041608749#u32,847828130#u32⟩,⟨1698118915#u32,1691076741#u32⟩⟩
def q022 : aspis_core.field.QM31 := ⟨⟨1819985108#u32,1775297862#u32⟩,⟨1866648082#u32,1549667231#u32⟩⟩
def q023 : aspis_core.field.QM31 := ⟨⟨576030860#u32,1960024758#u32⟩,⟨266706019#u32,1357022704#u32⟩⟩
def q024 : aspis_core.field.QM31 := ⟨⟨40105540#u32,1572894176#u32⟩,⟨1128859828#u32,1452095554#u32⟩⟩
def q025 : aspis_core.field.QM31 := ⟨⟨31707117#u32,1141605523#u32⟩,⟨1555692882#u32,675499391#u32⟩⟩
def q026 : aspis_core.field.QM31 := ⟨⟨1520023580#u32,1972807226#u32⟩,⟨213458520#u32,1570606483#u32⟩⟩
def q027 : aspis_core.field.QM31 := ⟨⟨839969315#u32,1393507838#u32⟩,⟨1451026085#u32,492151165#u32⟩⟩
def q028 : aspis_core.field.QM31 := ⟨⟨1606912134#u32,1109619845#u32⟩,⟨284438691#u32,1556286145#u32⟩⟩
def q029 : aspis_core.field.QM31 := ⟨⟨683248576#u32,1116339708#u32⟩,⟨571233103#u32,28574165#u32⟩⟩
def q030 : aspis_core.field.QM31 := ⟨⟨653014195#u32,2028303736#u32⟩,⟨96765549#u32,625260790#u32⟩⟩
def q031 : aspis_core.field.QM31 := ⟨⟨1978264032#u32,374047219#u32⟩,⟨1033323366#u32,1219729133#u32⟩⟩
def q032 : aspis_core.field.QM31 := ⟨⟨920851429#u32,679817331#u32⟩,⟨1805595538#u32,734494604#u32⟩⟩
def q033 : aspis_core.field.QM31 := ⟨⟨2113374400#u32,38706877#u32⟩,⟨173236851#u32,1567741503#u32⟩⟩
def q034 : aspis_core.field.QM31 := ⟨⟨1449894452#u32,2050554784#u32⟩,⟨1482004424#u32,283402702#u32⟩⟩
def q035 : aspis_core.field.QM31 := ⟨⟨1557341767#u32,2115349233#u32⟩,⟨190741495#u32,1395709799#u32⟩⟩
def q036 : aspis_core.field.QM31 := ⟨⟨986396648#u32,1390360427#u32⟩,⟨226373284#u32,1981296876#u32⟩⟩
def q037 : aspis_core.field.QM31 := ⟨⟨478477890#u32,88413742#u32⟩,⟨1008643515#u32,1926225968#u32⟩⟩
def q038 : aspis_core.field.QM31 := ⟨⟨1508721239#u32,532142070#u32⟩,⟨496162077#u32,1067769770#u32⟩⟩
def q039 : aspis_core.field.QM31 := ⟨⟨1229629430#u32,427293366#u32⟩,⟨466165733#u32,1508755227#u32⟩⟩
def q040 : aspis_core.field.QM31 := ⟨⟨1244565670#u32,2028127751#u32⟩,⟨1467128028#u32,273813827#u32⟩⟩
def q041 : aspis_core.field.QM31 := ⟨⟨115925539#u32,1864830689#u32⟩,⟨293254943#u32,760402556#u32⟩⟩
def q042 : aspis_core.field.QM31 := ⟨⟨316219052#u32,84633384#u32⟩,⟨1321551925#u32,1190764200#u32⟩⟩
def q043 : aspis_core.field.QM31 := ⟨⟨291345530#u32,1605824612#u32⟩,⟨1916306436#u32,2142653268#u32⟩⟩
def q044 : aspis_core.field.QM31 := ⟨⟨909007924#u32,1763388706#u32⟩,⟨395737900#u32,1338719020#u32⟩⟩
def q045 : aspis_core.field.QM31 := ⟨⟨890933737#u32,267245577#u32⟩,⟨882566552#u32,1385235435#u32⟩⟩
def q046 : aspis_core.field.QM31 := ⟨⟨1559895302#u32,936557391#u32⟩,⟨968123367#u32,1117152502#u32⟩⟩
def q047 : aspis_core.field.QM31 := ⟨⟨1083786783#u32,572692418#u32⟩,⟨1387193770#u32,1427045905#u32⟩⟩
def q048 : aspis_core.field.QM31 := ⟨⟨886314905#u32,153811235#u32⟩,⟨355016537#u32,1104678391#u32⟩⟩
def q049 : aspis_core.field.QM31 := ⟨⟨1895553284#u32,443112526#u32⟩,⟨2066850729#u32,369647826#u32⟩⟩
def q050 : aspis_core.field.QM31 := ⟨⟨574523712#u32,2071742302#u32⟩,⟨661144582#u32,2075999539#u32⟩⟩
def q051 : aspis_core.field.QM31 := ⟨⟨1563931643#u32,1035190939#u32⟩,⟨148837746#u32,1614674823#u32⟩⟩
def q052 : aspis_core.field.QM31 := ⟨⟨317302683#u32,1745571332#u32⟩,⟨420994753#u32,209217899#u32⟩⟩
def q053 : aspis_core.field.QM31 := ⟨⟨91667832#u32,1488000584#u32⟩,⟨253736320#u32,1265165655#u32⟩⟩
def q054 : aspis_core.field.QM31 := ⟨⟨36768370#u32,337267765#u32⟩,⟨443249262#u32,1261093033#u32⟩⟩
def q055 : aspis_core.field.QM31 := ⟨⟨697070129#u32,71212731#u32⟩,⟨925649290#u32,16130830#u32⟩⟩
def q056 : aspis_core.field.QM31 := ⟨⟨1456385046#u32,110387359#u32⟩,⟨946225430#u32,1943650850#u32⟩⟩
def q057 : aspis_core.field.QM31 := ⟨⟨817897036#u32,666294842#u32⟩,⟨283264643#u32,510729650#u32⟩⟩
def q058 : aspis_core.field.QM31 := ⟨⟨1311439999#u32,762425595#u32⟩,⟨1935542763#u32,1712192565#u32⟩⟩
def q059 : aspis_core.field.QM31 := ⟨⟨1311071148#u32,432280840#u32⟩,⟨1879367408#u32,1298847843#u32⟩⟩
def q060 : aspis_core.field.QM31 := ⟨⟨1469124469#u32,1697353213#u32⟩,⟨1619762236#u32,306855218#u32⟩⟩
def q061 : aspis_core.field.QM31 := ⟨⟨1141961392#u32,839058058#u32⟩,⟨1375318328#u32,319457268#u32⟩⟩
def q062 : aspis_core.field.QM31 := ⟨⟨2111819276#u32,2098213818#u32⟩,⟨85334860#u32,1886643229#u32⟩⟩
def q063 : aspis_core.field.QM31 := ⟨⟨1255131024#u32,2059651672#u32⟩,⟨1368910585#u32,2133248799#u32⟩⟩
def q064 : aspis_core.field.QM31 := ⟨⟨752548862#u32,474240349#u32⟩,⟨1192282096#u32,1466812857#u32⟩⟩
def q065 : aspis_core.field.QM31 := ⟨⟨1400288221#u32,1385129720#u32⟩,⟨1943770729#u32,686411351#u32⟩⟩
def q066 : aspis_core.field.QM31 := ⟨⟨1887908471#u32,1467564562#u32⟩,⟨1860597809#u32,1467676535#u32⟩⟩
def q067 : aspis_core.field.QM31 := ⟨⟨1459363803#u32,1635029942#u32⟩,⟨2099383213#u32,955973033#u32⟩⟩
def q068 : aspis_core.field.QM31 := ⟨⟨1829436582#u32,476636321#u32⟩,⟨749437642#u32,1018857315#u32⟩⟩
def q069 : aspis_core.field.QM31 := ⟨⟨1594698273#u32,1560300028#u32⟩,⟨1247792630#u32,1692799177#u32⟩⟩
def q070 : aspis_core.field.QM31 := ⟨⟨428872250#u32,2028150462#u32⟩,⟨1837172315#u32,1906487998#u32⟩⟩
def q071 : aspis_core.field.QM31 := ⟨⟨1329505147#u32,633471990#u32⟩,⟨1054039628#u32,45454168#u32⟩⟩
def q072 : aspis_core.field.QM31 := ⟨⟨772370642#u32,14922438#u32⟩,⟨1408466197#u32,1623710213#u32⟩⟩
def q073 : aspis_core.field.QM31 := ⟨⟨1410162484#u32,637324994#u32⟩,⟨569450230#u32,537546180#u32⟩⟩
def q074 : aspis_core.field.QM31 := ⟨⟨1157715339#u32,342057553#u32⟩,⟨1792842624#u32,1452808024#u32⟩⟩
def q075 : aspis_core.field.QM31 := ⟨⟨1532942618#u32,168998933#u32⟩,⟨586045330#u32,1139991344#u32⟩⟩
def q076 : aspis_core.field.QM31 := ⟨⟨1591879073#u32,1906731442#u32⟩,⟨1671962861#u32,379204847#u32⟩⟩
def q077 : aspis_core.field.QM31 := ⟨⟨680351639#u32,1240409503#u32⟩,⟨126536825#u32,537044462#u32⟩⟩
def q078 : aspis_core.field.QM31 := ⟨⟨1834938714#u32,377014235#u32⟩,⟨280591185#u32,740003598#u32⟩⟩
def q079 : aspis_core.field.QM31 := ⟨⟨860421153#u32,986740142#u32⟩,⟨282462356#u32,166514692#u32⟩⟩
def q080 : aspis_core.field.QM31 := ⟨⟨136576199#u32,1802040406#u32⟩,⟨1061503406#u32,611773292#u32⟩⟩
def q081 : aspis_core.field.QM31 := ⟨⟨955431445#u32,2030413322#u32⟩,⟨990889493#u32,472175021#u32⟩⟩
def q082 : aspis_core.field.QM31 := ⟨⟨927853130#u32,154515665#u32⟩,⟨1180143979#u32,816072254#u32⟩⟩
def q083 : aspis_core.field.QM31 := ⟨⟨493835551#u32,316413053#u32⟩,⟨72863175#u32,911228628#u32⟩⟩
def q084 : aspis_core.field.QM31 := ⟨⟨1354004346#u32,1508559680#u32⟩,⟨532698783#u32,166689039#u32⟩⟩
def q085 : aspis_core.field.QM31 := ⟨⟨1484121242#u32,719925025#u32⟩,⟨622190725#u32,1319408864#u32⟩⟩
def q086 : aspis_core.field.QM31 := ⟨⟨756256590#u32,1261812326#u32⟩,⟨145941036#u32,1331872486#u32⟩⟩
def q087 : aspis_core.field.QM31 := ⟨⟨180442422#u32,824552193#u32⟩,⟨1075997832#u32,2046928047#u32⟩⟩
def q088 : aspis_core.field.QM31 := ⟨⟨1449124181#u32,895619289#u32⟩,⟨1283482632#u32,1899810374#u32⟩⟩
def q089 : aspis_core.field.QM31 := ⟨⟨2041590681#u32,427602603#u32⟩,⟨1124735857#u32,122380468#u32⟩⟩
def q090 : aspis_core.field.QM31 := ⟨⟨965615933#u32,2103612420#u32⟩,⟨159248852#u32,78644047#u32⟩⟩
def q091 : aspis_core.field.QM31 := ⟨⟨1140382225#u32,1107504788#u32⟩,⟨1438746949#u32,15309227#u32⟩⟩
def q092 : aspis_core.field.QM31 := ⟨⟨1924037894#u32,1978604428#u32⟩,⟨1220506018#u32,309979002#u32⟩⟩
def q093 : aspis_core.field.QM31 := ⟨⟨1130852285#u32,631327962#u32⟩,⟨1685273369#u32,1413893324#u32⟩⟩
def q094 : aspis_core.field.QM31 := ⟨⟨1677761301#u32,1387974580#u32⟩,⟨1460485452#u32,835361249#u32⟩⟩
def q095 : aspis_core.field.QM31 := ⟨⟨1691887385#u32,1657243483#u32⟩,⟨1401095850#u32,80036066#u32⟩⟩
def q096 : aspis_core.field.QM31 := ⟨⟨1105971360#u32,128841052#u32⟩,⟨15610738#u32,288210253#u32⟩⟩
def q097 : aspis_core.field.QM31 := ⟨⟨1109092474#u32,1155555584#u32⟩,⟨277796012#u32,701540042#u32⟩⟩
def q098 : aspis_core.field.QM31 := ⟨⟨1243178829#u32,885149746#u32⟩,⟨679874714#u32,1593938463#u32⟩⟩
def q099 : aspis_core.field.QM31 := ⟨⟨1762577897#u32,1672037492#u32⟩,⟨2145023483#u32,1995708986#u32⟩⟩
def q100 : aspis_core.field.QM31 := ⟨⟨1403940980#u32,215090866#u32⟩,⟨1347647348#u32,1774997106#u32⟩⟩
def q101 : aspis_core.field.QM31 := ⟨⟨1403753062#u32,1148944380#u32⟩,⟨109914555#u32,746070928#u32⟩⟩
def q102 : aspis_core.field.QM31 := ⟨⟨1974752690#u32,2116530017#u32⟩,⟨1912238475#u32,381339612#u32⟩⟩
def q103 : aspis_core.field.QM31 := ⟨⟨16783966#u32,1555192431#u32⟩,⟨176777643#u32,584819280#u32⟩⟩
def q104 : aspis_core.field.QM31 := ⟨⟨665087372#u32,1166316795#u32⟩,⟨1185118411#u32,1369238671#u32⟩⟩
def q105 : aspis_core.field.QM31 := ⟨⟨404955804#u32,364514839#u32⟩,⟨427056206#u32,131649415#u32⟩⟩
def q106 : aspis_core.field.QM31 := ⟨⟨939234122#u32,502572768#u32⟩,⟨309121045#u32,247878045#u32⟩⟩
def q107 : aspis_core.field.QM31 := ⟨⟨945257057#u32,1081095575#u32⟩,⟨597309310#u32,1872756937#u32⟩⟩
def q108 : aspis_core.field.QM31 := ⟨⟨1252297121#u32,862816992#u32⟩,⟨1431392918#u32,102262519#u32⟩⟩
def q109 : aspis_core.field.QM31 := ⟨⟨762257405#u32,1725848444#u32⟩,⟨1894633764#u32,1541927454#u32⟩⟩
def q110 : aspis_core.field.QM31 := ⟨⟨78492650#u32,396385173#u32⟩,⟨1275357340#u32,1426218111#u32⟩⟩
def q111 : aspis_core.field.QM31 := ⟨⟨1833844415#u32,156629480#u32⟩,⟨997733724#u32,1113768152#u32⟩⟩
def q112 : aspis_core.field.QM31 := ⟨⟨1076513376#u32,228011114#u32⟩,⟨272309447#u32,1000050388#u32⟩⟩
def q113 : aspis_core.field.QM31 := ⟨⟨392715325#u32,1860833200#u32⟩,⟨1117226575#u32,810507807#u32⟩⟩
def q114 : aspis_core.field.QM31 := ⟨⟨1848614838#u32,1589541683#u32⟩,⟨1109005417#u32,327354693#u32⟩⟩
def q115 : aspis_core.field.QM31 := ⟨⟨29830584#u32,496441005#u32⟩,⟨563440420#u32,1626102052#u32⟩⟩
def a0 : Array aspis_core.field.QM31 29#usize := ⟨[q000,q001,q002,q003,q004,q005,q006,q007,q008,q009,q010,q011,q012,q013,q014,q015,q016,q017,q018,q019,q020,q021,q022,q023,q024,q025,q026,q027,q028],by rfl⟩
def a1 : Array aspis_core.field.QM31 29#usize := ⟨[q029,q030,q031,q032,q033,q034,q035,q036,q037,q038,q039,q040,q041,q042,q043,q044,q045,q046,q047,q048,q049,q050,q051,q052,q053,q054,q055,q056,q057],by rfl⟩
def a2 : Array aspis_core.field.QM31 29#usize := ⟨[q058,q059,q060,q061,q062,q063,q064,q065,q066,q067,q068,q069,q070,q071,q072,q073,q074,q075,q076,q077,q078,q079,q080,q081,q082,q083,q084,q085,q086],by rfl⟩
def a3 : Array aspis_core.field.QM31 29#usize := ⟨[q087,q088,q089,q090,q091,q092,q093,q094,q095,q096,q097,q098,q099,q100,q101,q102,q103,q104,q105,q106,q107,q108,q109,q110,q111,q112,q113,q114,q115],by rfl⟩
def claims : ClaimsUnrolledFinish.MainClaims := ⟨[a0,a1,a2],by rfl⟩
end AspisR1.JFu_ClaimsData
