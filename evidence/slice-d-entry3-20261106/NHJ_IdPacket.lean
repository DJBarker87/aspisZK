import NHJ_IdReference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NHJ_IdPacket
open Aeneas Aeneas.Std Result
abbrev KeyBytes := Array U8 32#usize
def poolDevnet : KeyBytes := Array.make 32#usize [160#u8, 19#u8, 98#u8, 42#u8, 240#u8, 202#u8, 109#u8, 154#u8, 218#u8, 233#u8, 162#u8, 167#u8, 169#u8, 176#u8, 187#u8, 66#u8, 122#u8, 69#u8, 190#u8, 75#u8, 195#u8, 45#u8, 233#u8, 50#u8, 40#u8, 58#u8, 26#u8, 66#u8, 26#u8, 133#u8, 145#u8, 52#u8]
def registryDevnet : KeyBytes := Array.make 32#usize [131#u8, 9#u8, 163#u8, 201#u8, 153#u8, 45#u8, 35#u8, 222#u8, 189#u8, 104#u8, 139#u8, 224#u8, 185#u8, 96#u8, 72#u8, 135#u8, 226#u8, 88#u8, 106#u8, 68#u8, 10#u8, 156#u8, 60#u8, 72#u8, 82#u8, 28#u8, 53#u8, 49#u8, 227#u8, 146#u8, 232#u8, 171#u8]
def poolDefault : KeyBytes := Array.repeat 32#usize 65#u8
def registryDefault : KeyBytes := Array.repeat 32#usize 68#u8
def pool (devnet : Bool) : KeyBytes := if devnet then poolDevnet else poolDefault
def registry (devnet : Bool) : KeyBytes := if devnet then registryDevnet else registryDefault

/-- Packet constants for the two pinned loaded images. Other operations are
unchanged; this definition does not assert that arbitrary Ops implement IDs. -/
def install (ops : AdapterRw.Ops) (devnet : Bool) : AdapterRw.Ops :=
  {ops with op45 := ok (pool devnet), op46 := ok (registry devnet)}

theorem extracted (devnet : Bool) : NHJ_IdReference.ids_ref devnet =
    ok (Array.make 2#usize [pool devnet,registry devnet]) := by
  cases devnet <;> rfl

theorem pool_slot (ops : AdapterRw.Ops) (devnet : Bool) :
    (install ops devnet).op45 = ok (pool devnet) := rfl

theorem registry_slot (ops : AdapterRw.Ops) (devnet : Bool) :
    (install ops devnet).op46 = ok (registry devnet) := rfl

theorem digest_preserved (ops : AdapterRw.Ops) (devnet : Bool) :
    (install ops devnet).op43 = ops.op43 := rfl

theorem error_preserved (ops : AdapterRw.Ops) (devnet : Bool) :
    (install ops devnet).op44 = ops.op44 := rfl
#print axioms extracted
#print axioms pool_slot
#print axioms registry_slot
#print axioms digest_preserved
#print axioms error_preserved
end NHJ_IdPacket
