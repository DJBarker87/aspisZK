import Aeneas
open Aeneas Aeneas.Std
namespace PV_UC_StringEntry
-- Frozen crates/aspis-core/src/field.rs:19, pub const P: u32 = 0x7fff_ffff.
-- Aeneas's constant access has a Result wrapper; the literal cannot fail.
def aspis_core.field.P : Result U32 := .ok 2147483647#u32
#print axioms aspis_core.field.P
end PV_UC_StringEntry
