import Aeneas
open Aeneas Aeneas.Std
/-- Pinned SDK Pubkey carrier; callers retain all32 bytes. -/
abbrev NMT_stage1_owned.solana_pubkey.Pubkey := Array U8 32#usize
