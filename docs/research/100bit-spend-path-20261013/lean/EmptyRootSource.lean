import OccupancyGeneratedSlice
import SelectorArrayMapSuccess

/-! Exact frozen table and empty_root helper from the sealed candidate.
Namespace framing only; original source declarations are byte-for-byte. -/
open Aeneas Aeneas.Std Result
namespace AspisR1EmptyRootCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::field::M31]:
    Source: 'src/field.rs', lines 23:0-23:24 -/
def field.M31_constructor (i : Std.U32) : Result field.M31 := do
  ok i

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::constants::POOL_V1_PAIR_EMPTY_ROOTS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal_constants.rs', lines 2:0-24:2
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  : Array (Array Std.U32 8#usize) 21#usize :=
  Array.make 21#usize [
    Array.make 8#usize [
      1438900896#u32, 782233260#u32, 1544844157#u32, 891350894#u32,
      986827501#u32, 300047813#u32, 266092546#u32, 1155026732#u32
      ],
    Array.make 8#usize [
      141619947#u32, 1448060902#u32, 524379093#u32, 1944458907#u32,
      1832113773#u32, 579270723#u32, 752346270#u32, 1038346536#u32
      ],
    Array.make 8#usize [
      1119858538#u32, 128294437#u32, 939091034#u32, 659145897#u32,
      1933666768#u32, 903679201#u32, 1182639487#u32, 1398246146#u32
      ],
    Array.make 8#usize [
      1057897051#u32, 1132946363#u32, 794377079#u32, 1971564389#u32,
      1255722275#u32, 926653737#u32, 2031728153#u32, 2024887573#u32
      ],
    Array.make 8#usize [
      1410054462#u32, 673771449#u32, 940847521#u32, 274330358#u32,
      1719505495#u32, 1690439941#u32, 203201419#u32, 1855504616#u32
      ],
    Array.make 8#usize [
      1442759752#u32, 1540325866#u32, 188964047#u32, 101815282#u32,
      1883549730#u32, 1774537487#u32, 1306717763#u32, 561084592#u32
      ],
    Array.make 8#usize [
      244193611#u32, 984304317#u32, 1467689208#u32, 2063463197#u32,
      1766003332#u32, 1300835127#u32, 1578947755#u32, 745931587#u32
      ],
    Array.make 8#usize [
      673192756#u32, 38070812#u32, 1453532835#u32, 1340577407#u32,
      368420458#u32, 1834405704#u32, 270061815#u32, 711700631#u32
      ],
    Array.make 8#usize [
      27092219#u32, 1272373356#u32, 998194489#u32, 1458413288#u32,
      887470405#u32, 1204987730#u32, 864453460#u32, 553704718#u32
      ],
    Array.make 8#usize [
      1972918328#u32, 1234090299#u32, 977162835#u32, 1704494754#u32,
      1617603773#u32, 1819200880#u32, 906453206#u32, 1653526885#u32
      ],
    Array.make 8#usize [
      418360492#u32, 472096212#u32, 871749117#u32, 98906847#u32,
      2026788776#u32, 1504737042#u32, 407274798#u32, 1800828893#u32
      ],
    Array.make 8#usize [
      986339640#u32, 660349625#u32, 1012157959#u32, 454024326#u32,
      987656904#u32, 622864739#u32, 1150440730#u32, 1280042062#u32
      ],
    Array.make 8#usize [
      2118470693#u32, 1706590589#u32, 2128512933#u32, 167263577#u32,
      409542414#u32, 1323179656#u32, 1880070613#u32, 2053396184#u32
      ],
    Array.make 8#usize [
      260546973#u32, 1375125357#u32, 1584234519#u32, 1097072342#u32,
      1685367984#u32, 1070989054#u32, 2113798037#u32, 958210542#u32
      ],
    Array.make 8#usize [
      1239966481#u32, 992485427#u32, 1397515674#u32, 466658549#u32,
      2071909237#u32, 712995354#u32, 2047452742#u32, 1680224983#u32
      ],
    Array.make 8#usize [
      1796237568#u32, 1862343136#u32, 1954463912#u32, 1190686266#u32,
      364700025#u32, 46960257#u32, 671215600#u32, 1214723477#u32
      ],
    Array.make 8#usize [
      1127845264#u32, 662862400#u32, 84021756#u32, 995080286#u32,
      1419670571#u32, 1966281459#u32, 837284626#u32, 2083375353#u32
      ],
    Array.make 8#usize [
      1321679286#u32, 782621548#u32, 1415820264#u32, 74436574#u32,
      776350425#u32, 323154748#u32, 429051705#u32, 1299980413#u32
      ],
    Array.make 8#usize [
      1519171444#u32, 1235587172#u32, 1671492368#u32, 1449613582#u32,
      547369941#u32, 1621086153#u32, 266860322#u32, 450526803#u32
      ],
    Array.make 8#usize [
      19381883#u32, 1308966873#u32, 251977766#u32, 474343397#u32,
      2069732268#u32, 1863820229#u32, 152153379#u32, 665567443#u32
      ],
    Array.make 8#usize [
      1201428963#u32, 1296676114#u32, 441891487#u32, 1910121140#u32,
      602621674#u32, 1294160489#u32, 1878016864#u32, 855887413#u32
      ]
    ]

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::empty_root]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 179:0-181:1 -/
def pool_v1.pair_forest_semantic_terminal.empty_root
  (level : Std.Usize) : Result (Array field.M31 8#usize) := do
  let a ←
    Array.index_usize
      pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
      level
  core.array.Array.map (BuiltinFnMut Std.U32 field.M31) a
    (field.M31_constructor)

end AspisR1EmptyRootCandidate
