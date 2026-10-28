import Aeneas
set_option autoImplicit false
namespace PDict_ConstantsSource
open Aeneas Aeneas.Std Result

/-- [aspis_r1_cost_probe::multiproof::LEAF_BITS]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/multiproof.rs', lines 18:0-18:24
    Name pattern: [aspis_r1_cost_probe::multiproof::LEAF_BITS]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_r1_cost_probe::multiproof::LEAF_BITS"]
def aspis_r1_cost_probe.multiproof.LEAF_BITS : Std.U32 := 18#u32

/-- [aspis_r1_cost_probe::multiproof::MAX_BATCH]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/multiproof.rs', lines 23:0-23:26
    Name pattern: [aspis_r1_cost_probe::multiproof::MAX_BATCH]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_r1_cost_probe::multiproof::MAX_BATCH"]
def aspis_r1_cost_probe.multiproof.MAX_BATCH : Std.Usize := 16#usize

/-- [aspis_r1_cost_probe::r1_wire::DOMAIN]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 12:0-12:23
    Name pattern: [aspis_r1_cost_probe::r1_wire::DOMAIN]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_r1_cost_probe::r1_wire::DOMAIN"]
def aspis_r1_cost_probe.r1_wire.DOMAIN : Slice Std.U8 :=
  Array.to_slice
    (Array.make 38#usize [
      85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
      49#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8, 84#u8, 69#u8, 45#u8,
      83#u8, 65#u8, 76#u8, 84#u8, 69#u8, 68#u8, 58#u8, 83#u8, 69#u8, 77#u8,
      65#u8, 78#u8, 84#u8, 73#u8, 67#u8, 58#u8, 80#u8, 51#u8
      ])

/-- [aspis_r1_cost_probe::r1_wire::LANES]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 13:0-13:22
    Name pattern: [aspis_r1_cost_probe::r1_wire::LANES]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_r1_cost_probe::r1_wire::LANES"]
def aspis_r1_cost_probe.r1_wire.LANES : Std.Usize := 29#usize

/-- [aspis_r1_cost_probe::r1_wire::POINTS]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 14:0-14:23
    Name pattern: [aspis_r1_cost_probe::r1_wire::POINTS]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_r1_cost_probe::r1_wire::POINTS"]
def aspis_r1_cost_probe.r1_wire.POINTS : Std.Usize := 3#usize

/-- [aspis_r1_cost_probe::r1_wire::CLAIMS]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 15:0-15:23
    Name pattern: [aspis_r1_cost_probe::r1_wire::CLAIMS]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_r1_cost_probe::r1_wire::CLAIMS"]
def aspis_r1_cost_probe.r1_wire.CLAIMS : Result Std.Usize :=
  aspis_r1_cost_probe.r1_wire.POINTS * aspis_r1_cost_probe.r1_wire.LANES

/-- [pdict_pure::leaf_bits]:
    Source: 'lib.rs', lines 13:0-13:70
    Visibility: public -/
def leaf_bits : Result Std.U32 := do
  ok aspis_r1_cost_probe.multiproof.LEAF_BITS

/-- [pdict_pure::max_batch]:
    Source: 'lib.rs', lines 15:0-15:72
    Visibility: public -/
def max_batch : Result Std.Usize := do
  ok aspis_r1_cost_probe.multiproof.MAX_BATCH

/-- [pdict_pure::lanes]:
    Source: 'lib.rs', lines 17:0-17:61
    Visibility: public -/
def lanes : Result Std.Usize := do
  ok aspis_r1_cost_probe.r1_wire.LANES

/-- [pdict_pure::claims]:
    Source: 'lib.rs', lines 19:0-19:63
    Visibility: public -/
def claims : Result Std.Usize := do
  aspis_r1_cost_probe.r1_wire.CLAIMS

/-- [pdict_pure::domain]:
    Source: 'lib.rs', lines 21:0-21:71
    Visibility: public -/
def domain : Result (Slice Std.U8) := do
  ok aspis_r1_cost_probe.r1_wire.DOMAIN


#print axioms aspis_r1_cost_probe.multiproof.LEAF_BITS
#print axioms aspis_r1_cost_probe.multiproof.MAX_BATCH
#print axioms aspis_r1_cost_probe.r1_wire.DOMAIN
#print axioms aspis_r1_cost_probe.r1_wire.LANES
#print axioms aspis_r1_cost_probe.r1_wire.POINTS
#print axioms aspis_r1_cost_probe.r1_wire.CLAIMS
#print axioms leaf_bits
#print axioms max_batch
#print axioms lanes
#print axioms claims
#print axioms domain
end PDict_ConstantsSource
