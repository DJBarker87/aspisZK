import R1Z.PV_Src_NativeInput
import R1Z.PV_RunJoin_RecordedTransfer
import R1Z.PV_RunJoin_RecordedWithdrawal

/-! Literal argument carriers from the pinned deterministic native probe.
This file supplies no compilation payload and proves no fixture-generator,
compiler-return, parser, or deployed-selection equation. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FixtureArguments
open Aeneas Aeneas.Std
open BuilderForestAdmissionPort.pool_v1

def witness : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1 where
 pair := {
 nullifier_key := Array.make 8#usize [11#u32, 28#u32, 45#u32, 62#u32, 79#u32, 96#u32, 113#u32, 130#u32]
 salt := Array.make 8#usize [101#u32, 118#u32, 135#u32, 152#u32, 169#u32, 186#u32, 203#u32, 220#u32]
 value := 1000#u32
 pair_leaf := {
 first_commitment := Array.make 8#usize [2028667570#u32, 45893279#u32, 894642502#u32, 1930282162#u32, 1562116262#u32, 823639309#u32, 745717450#u32, 1034934647#u32]
 second_occupied := 1#u32
 second_commitment := Array.make 8#usize [901#u32, 918#u32, 935#u32, 952#u32, 969#u32, 986#u32, 1003#u32, 1020#u32]
 second_occupancy_inverse := 541081664#u32 }
 selected_second := false
 membership := {
 siblings := Array.make 20#usize [
Array.make 8#usize [2001#u32, 2018#u32, 2035#u32, 2052#u32, 2069#u32, 2086#u32, 2103#u32, 2120#u32],
Array.make 8#usize [2021#u32, 2038#u32, 2055#u32, 2072#u32, 2089#u32, 2106#u32, 2123#u32, 2140#u32],
Array.make 8#usize [2041#u32, 2058#u32, 2075#u32, 2092#u32, 2109#u32, 2126#u32, 2143#u32, 2160#u32],
Array.make 8#usize [2061#u32, 2078#u32, 2095#u32, 2112#u32, 2129#u32, 2146#u32, 2163#u32, 2180#u32],
Array.make 8#usize [2081#u32, 2098#u32, 2115#u32, 2132#u32, 2149#u32, 2166#u32, 2183#u32, 2200#u32],
Array.make 8#usize [2101#u32, 2118#u32, 2135#u32, 2152#u32, 2169#u32, 2186#u32, 2203#u32, 2220#u32],
Array.make 8#usize [2121#u32, 2138#u32, 2155#u32, 2172#u32, 2189#u32, 2206#u32, 2223#u32, 2240#u32],
Array.make 8#usize [2141#u32, 2158#u32, 2175#u32, 2192#u32, 2209#u32, 2226#u32, 2243#u32, 2260#u32],
Array.make 8#usize [2161#u32, 2178#u32, 2195#u32, 2212#u32, 2229#u32, 2246#u32, 2263#u32, 2280#u32],
Array.make 8#usize [2181#u32, 2198#u32, 2215#u32, 2232#u32, 2249#u32, 2266#u32, 2283#u32, 2300#u32],
Array.make 8#usize [2201#u32, 2218#u32, 2235#u32, 2252#u32, 2269#u32, 2286#u32, 2303#u32, 2320#u32],
Array.make 8#usize [2221#u32, 2238#u32, 2255#u32, 2272#u32, 2289#u32, 2306#u32, 2323#u32, 2340#u32],
Array.make 8#usize [2241#u32, 2258#u32, 2275#u32, 2292#u32, 2309#u32, 2326#u32, 2343#u32, 2360#u32],
Array.make 8#usize [2261#u32, 2278#u32, 2295#u32, 2312#u32, 2329#u32, 2346#u32, 2363#u32, 2380#u32],
Array.make 8#usize [2281#u32, 2298#u32, 2315#u32, 2332#u32, 2349#u32, 2366#u32, 2383#u32, 2400#u32],
Array.make 8#usize [2301#u32, 2318#u32, 2335#u32, 2352#u32, 2369#u32, 2386#u32, 2403#u32, 2420#u32],
Array.make 8#usize [2321#u32, 2338#u32, 2355#u32, 2372#u32, 2389#u32, 2406#u32, 2423#u32, 2440#u32],
Array.make 8#usize [2341#u32, 2358#u32, 2375#u32, 2392#u32, 2409#u32, 2426#u32, 2443#u32, 2460#u32],
Array.make 8#usize [2361#u32, 2378#u32, 2395#u32, 2412#u32, 2429#u32, 2446#u32, 2463#u32, 2480#u32],
Array.make 8#usize [2381#u32, 2398#u32, 2415#u32, 2432#u32, 2449#u32, 2466#u32, 2483#u32, 2500#u32]]
 index := 344865#u32 } }
 super_root_siblings := Array.make 3#usize [Array.make 8#usize [3001#u32, 3018#u32, 3035#u32, 3052#u32, 3069#u32, 3086#u32, 3103#u32, 3120#u32], Array.make 8#usize [3101#u32, 3118#u32, 3135#u32, 3152#u32, 3169#u32, 3186#u32, 3203#u32, 3220#u32], Array.make 8#usize [3201#u32, 3218#u32, 3235#u32, 3252#u32, 3269#u32, 3286#u32, 3303#u32, 3320#u32]]
 super_root_directions := Array.make 3#usize [true,false,true]

def snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1 where
 pool := PV_RunJoin_RecordedTransfer.publicRecord.pool
 deployment_domain := PV_RunJoin_RecordedTransfer.publicRecord.deployment_domain
 sequence := 0#u64
 next_pair_index := 0#u64
 current_root := Array.make 8#usize [1201428963#u32, 1296676114#u32, 441891487#u32, 1910121140#u32, 602621674#u32, 1294160489#u32, 1878016864#u32, 855887413#u32]
 frontier := Array.make 20#usize [
Array.make 8#usize [1438900896#u32, 782233260#u32, 1544844157#u32, 891350894#u32, 986827501#u32, 300047813#u32, 266092546#u32, 1155026732#u32],
Array.make 8#usize [141619947#u32, 1448060902#u32, 524379093#u32, 1944458907#u32, 1832113773#u32, 579270723#u32, 752346270#u32, 1038346536#u32],
Array.make 8#usize [1119858538#u32, 128294437#u32, 939091034#u32, 659145897#u32, 1933666768#u32, 903679201#u32, 1182639487#u32, 1398246146#u32],
Array.make 8#usize [1057897051#u32, 1132946363#u32, 794377079#u32, 1971564389#u32, 1255722275#u32, 926653737#u32, 2031728153#u32, 2024887573#u32],
Array.make 8#usize [1410054462#u32, 673771449#u32, 940847521#u32, 274330358#u32, 1719505495#u32, 1690439941#u32, 203201419#u32, 1855504616#u32],
Array.make 8#usize [1442759752#u32, 1540325866#u32, 188964047#u32, 101815282#u32, 1883549730#u32, 1774537487#u32, 1306717763#u32, 561084592#u32],
Array.make 8#usize [244193611#u32, 984304317#u32, 1467689208#u32, 2063463197#u32, 1766003332#u32, 1300835127#u32, 1578947755#u32, 745931587#u32],
Array.make 8#usize [673192756#u32, 38070812#u32, 1453532835#u32, 1340577407#u32, 368420458#u32, 1834405704#u32, 270061815#u32, 711700631#u32],
Array.make 8#usize [27092219#u32, 1272373356#u32, 998194489#u32, 1458413288#u32, 887470405#u32, 1204987730#u32, 864453460#u32, 553704718#u32],
Array.make 8#usize [1972918328#u32, 1234090299#u32, 977162835#u32, 1704494754#u32, 1617603773#u32, 1819200880#u32, 906453206#u32, 1653526885#u32],
Array.make 8#usize [418360492#u32, 472096212#u32, 871749117#u32, 98906847#u32, 2026788776#u32, 1504737042#u32, 407274798#u32, 1800828893#u32],
Array.make 8#usize [986339640#u32, 660349625#u32, 1012157959#u32, 454024326#u32, 987656904#u32, 622864739#u32, 1150440730#u32, 1280042062#u32],
Array.make 8#usize [2118470693#u32, 1706590589#u32, 2128512933#u32, 167263577#u32, 409542414#u32, 1323179656#u32, 1880070613#u32, 2053396184#u32],
Array.make 8#usize [260546973#u32, 1375125357#u32, 1584234519#u32, 1097072342#u32, 1685367984#u32, 1070989054#u32, 2113798037#u32, 958210542#u32],
Array.make 8#usize [1239966481#u32, 992485427#u32, 1397515674#u32, 466658549#u32, 2071909237#u32, 712995354#u32, 2047452742#u32, 1680224983#u32],
Array.make 8#usize [1796237568#u32, 1862343136#u32, 1954463912#u32, 1190686266#u32, 364700025#u32, 46960257#u32, 671215600#u32, 1214723477#u32],
Array.make 8#usize [1127845264#u32, 662862400#u32, 84021756#u32, 995080286#u32, 1419670571#u32, 1966281459#u32, 837284626#u32, 2083375353#u32],
Array.make 8#usize [1321679286#u32, 782621548#u32, 1415820264#u32, 74436574#u32, 776350425#u32, 323154748#u32, 429051705#u32, 1299980413#u32],
Array.make 8#usize [1519171444#u32, 1235587172#u32, 1671492368#u32, 1449613582#u32, 547369941#u32, 1621086153#u32, 266860322#u32, 450526803#u32],
Array.make 8#usize [19381883#u32, 1308966873#u32, 251977766#u32, 474343397#u32, 2069732268#u32, 1863820229#u32, 152153379#u32, 665567443#u32]]

def recipient : payment_relation.PoolV1OutputNoteWitnessV1 :=
  ⟨Array.make 8#usize [301#u32, 318#u32, 335#u32, 352#u32, 369#u32, 386#u32, 403#u32, 420#u32], Array.make 8#usize [401#u32, 418#u32, 435#u32, 452#u32, 469#u32, 486#u32, 503#u32, 520#u32], 600#u32⟩

def transferChange : payment_relation.PoolV1OutputNoteWitnessV1 :=
  ⟨Array.make 8#usize [501#u32, 518#u32, 535#u32, 552#u32, 569#u32, 586#u32, 603#u32, 620#u32], Array.make 8#usize [601#u32, 618#u32, 635#u32, 652#u32, 669#u32, 686#u32, 703#u32, 720#u32], 400#u32⟩

def withdrawalChange : payment_relation.PoolV1OutputNoteWitnessV1 :=
  ⟨Array.make 8#usize [701#u32, 718#u32, 735#u32, 752#u32, 769#u32, 786#u32, 803#u32, 820#u32], Array.make 8#usize [801#u32, 818#u32, 835#u32, 852#u32, 869#u32, 886#u32, 903#u32, 920#u32], 750#u32⟩

def laneAnchor : Array U32 8#usize := Array.make 8#usize [9991919#u32, 1366070145#u32, 2057247444#u32, 1742688934#u32, 729806222#u32, 499041299#u32, 1681224112#u32, 1485431753#u32]

def transferRequest : PV_Src_NativeInput.Request :=
 .transfer PV_RunJoin_RecordedTransfer.publicRecord recipient

def withdrawalRequest : PV_Src_NativeInput.Request :=
 .withdrawal PV_RunJoin_RecordedWithdrawal.publicRecord

#print axioms witness
#print axioms snapshot
#print axioms recipient
#print axioms transferChange
#print axioms withdrawalChange
#print axioms laneAnchor
#print axioms transferRequest
#print axioms withdrawalRequest
end R1Z.PV_RunJoin_FixtureArguments
