import PoseidonLeadingSourceDeclarationsV5

/-! Exact missing tables from Funs SHA f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c. -/
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result

/-- [aspis_r1_mask_extraction_probe::poseidon2::EXTERNAL_FINAL]
    Source: 'src/statement/poseidon2.rs', lines 106:0-127:2 -/
@[global_simps, irreducible]
def poseidon2.EXTERNAL_FINAL : Array (Array Std.U32 16#usize) 4#usize :=
  Array.make 4#usize [
    Array.make 16#usize [
      1460209171#u32, 530850056#u32, 398192464#u32, 536338716#u32,
      75179210#u32, 1309934197#u32, 1335920373#u32, 127611036#u32,
      291093831#u32, 1832379621#u32, 123571662#u32, 303176864#u32,
      2137685056#u32, 1759609530#u32, 1418928155#u32, 71608334#u32
      ],
    Array.make 16#usize [
      6616262#u32, 1684515814#u32, 1721194338#u32, 720801691#u32,
      878392254#u32, 460379263#u32, 87930647#u32, 940673483#u32,
      1136203256#u32, 551499412#u32, 256220454#u32, 2007034235#u32,
      796124985#u32, 410436345#u32, 1705042586#u32, 1286336446#u32
      ],
    Array.make 16#usize [
      1522340456#u32, 1295296352#u32, 309794713#u32, 1772145068#u32,
      956898901#u32, 2137070800#u32, 988829146#u32, 2059451359#u32,
      1846491684#u32, 1105442551#u32, 1236497773#u32, 1452000568#u32,
      549485016#u32, 385992492#u32, 1987107948#u32, 1514377269#u32
      ],
    Array.make 16#usize [
      2090065934#u32, 1444920141#u32, 293113979#u32, 41120774#u32,
      855319793#u32, 1663284746#u32, 1789994008#u32, 1120509162#u32,
      358222743#u32, 1406256810#u32, 735183687#u32, 664485235#u32,
      1331641456#u32, 38121324#u32, 595810771#u32, 1234594393#u32
      ]
    ]

/-- [aspis_r1_mask_extraction_probe::poseidon2::INTERNAL]
    Source: 'src/statement/poseidon2.rs', lines 129:0-132:2 -/
@[global_simps, irreducible]
def poseidon2.INTERNAL : Array Std.U32 14#usize :=
  Array.make 14#usize [
    2139014335#u32, 69309039#u32, 1368974953#u32, 886780232#u32,
    1130937085#u32, 1718115455#u32, 2027103386#u32, 1612216449#u32,
    1994053242#u32, 110146615#u32, 514413329#u32, 1088763546#u32,
    955319292#u32, 488794657#u32
    ]


end AspisR1SelectedMaskProbe
