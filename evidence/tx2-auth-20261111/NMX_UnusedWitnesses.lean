import NMX_OwnedPackets
set_option autoImplicit false
namespace NMX_UnusedWitnesses
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets
/-- Only witnesses for unused forall binders in the first occurrence generator.
They are NEVER substituted for a native child reply, payload, or allocation. -/
def master : Box Master :=
 ⟨0,⟨0#u8,
  ⟨Array.repeat 32#usize 0#u8,Array.repeat 32#usize 0#u8,
   Array.repeat 32#usize 0#u8,0#u32,Array.repeat 32#usize 0#u8⟩,
  ⟨0#u8,Array.repeat 32#usize 0#u8,Array.repeat 32#usize 0#u8,Array.repeat 32#usize 0#u8⟩,
  0#u8,false,0#u64,Array.repeat 8#usize 0#u64⟩⟩
def checkpoint : Box Checkpoint :=
 ⟨0,⟨0#u8,Array.repeat 32#usize 0#u8,Array.repeat 32#usize 0#u8,
  0#u64,Array.repeat 8#usize 0#u32,Array.repeat 8#usize 0#u64⟩⟩
def lane : Box Lane :=
 ⟨0,⟨0#u8,Array.repeat 32#usize 0#u8,0#u8,
  ⟨0#u64,Array.repeat 8#usize 0#u32,
   Array.repeat 20#usize (Array.repeat 8#usize 0#u32)⟩⟩⟩
end NMX_UnusedWitnesses
