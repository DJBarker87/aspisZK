import PV_B3Q_TableTypes
namespace PV_B3Q_FrozenTables
def links8 : List Link := [(0,0,(998,0,1),(876,0,1)),
(0,0,(998,1,13),(864,0,10)),
(0,0,(875,0,1),(1001,0,12)),
(0,0,(1002,0,1),(892,0,1)),
(0,0,(1002,1,13),(880,0,10)),
(0,0,(891,0,1),(1005,0,12)),
(0,0,(1006,0,1),(908,0,1)),
(0,0,(1006,1,13),(896,0,10))]
theorem links8_safe : links8.all linkSafe = true := by decide
#print axioms links8_safe
end PV_B3Q_FrozenTables
