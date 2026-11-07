import Aeneas
open Aeneas Aeneas.Std
/-- Pinned SDK Hash is a32-byte value, interpreted under the existing SDK item.
No digest-value law is introduced here. -/
abbrev NMT_first.solana_hash.Hash := Array U8 32#usize
