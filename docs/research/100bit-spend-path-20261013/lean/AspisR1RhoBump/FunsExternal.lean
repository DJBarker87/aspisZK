import AspisR1RhoBump.Types
namespace AspisR1RhoBump
open Aeneas Aeneas.Std Result
-- Source ABI boundary: only *mut u8 is instantiated by this extraction.
class SourceSizeOf (T : Type) where
  bytes : Usize
instance pointerLayout : SourceSizeOf (MutRawPtr U8) := ⟨8#usize⟩
def core.mem.size_of (T : Type) [SourceSizeOf T] : Result Usize := .ok (SourceSizeOf.bytes (T:=T))
end AspisR1RhoBump
