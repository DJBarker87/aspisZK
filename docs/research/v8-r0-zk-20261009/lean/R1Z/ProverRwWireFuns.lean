import R1Z.ProverRwWireTypes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace ProverRwWire

/-- [aspis_r1_cost_probe::host_wire::{aspis_r1_cost_probe::host_wire::SemanticTranscript<H>}::sample_block_validated]:
    Source: 'crates/aspis-r1-cost-probe/src/host_wire.rs', lines 72:4-86:5 -/
def host_wire.SemanticTranscript.sample_block_validated
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H) (row : Std.U8)
  (framed : Slice Std.U8) :
  Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (host_wire.SemanticTranscript H))
  := do
  if row != self.next_row
  then
    ok (core.result.Result.Err (r1_wire.Error.RowOrder self.next_row row),
      self)
  else
    let s ← lift (Array.to_slice self.state)
    let i ← lift (Std.U8.wrapping_add 160#u8 row)
    let s1 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
    let s2 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, framed ]))
    let absorbed ← aspis_coredigestDigest32Inst.digest self.hash s2
    let s3 ← lift (Array.to_slice absorbed)
    let s4 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
    let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
    let block ← aspis_coredigestDigest32Inst.digest self.hash s5
    let s6 ← lift (Array.to_slice absorbed)
    let s7 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
    let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
    let a ← aspis_coredigestDigest32Inst.digest self.hash s8
    let i1 ← lift (Std.U8.wrapping_add self.next_row 1#u8)
    ok (core.result.Result.Ok block, { self with state := a, next_row := i1 })

end ProverRwWire
