import RPz7_S1SemanticFinishModelV1
import RPz7_S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def sampleBlock
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8)
  :
  Code ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  if row != self.next_row
  then
    pure (core.result.Result.Err (r1_wire.Error.RowOrder self.next_row row),
      self)
  else
    let s ← lift (Array.to_slice self.state)
    let i ← 160#u8 + row
    let s1 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
    let s2 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, framed ]))
    let absorbed ← PreparedHashCode.effects.digest aspis_coreDigest32Inst self.hash s2
    let s3 ← lift (Array.to_slice absorbed)
    let s4 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
    let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
    let block ← PreparedHashCode.effects.digest aspis_coreDigest32Inst self.hash s5
    let s6 ← lift (Array.to_slice absorbed)
    let s7 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
    let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
    let a ← PreparedHashCode.effects.digest aspis_coreDigest32Inst self.hash s8
    let i1 ← self.next_row + 1#u8
    pure (core.result.Result.Ok block, { self with state := a, next_row := i1 })

#print axioms sampleBlock
end AspisR1PublicPreparation.S1SemanticCode
