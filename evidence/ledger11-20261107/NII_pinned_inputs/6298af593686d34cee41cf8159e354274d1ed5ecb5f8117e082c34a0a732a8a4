import NGQ_Normalize
import NGQ_ArrayStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_MaterializeChain
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
abbrev Bytes32 := NGQ_Effects.Bytes32
abbrev Blocks := NGQ_Effects.Blocks

def parts (state : Bytes32) (tag : U8) : Parts := Array.to_slice
 (Array.make 2#usize [Array.to_slice state,Array.to_slice (Array.make 1#usize [tag])])

def pair (index : Usize) (blocks advances : Blocks) (state : Bytes32) :
    Code (Blocks × Blocks × Bytes32) := do
 let block ← CheckpointBytes5Effect.read (parts state 1#u8)
 let advance ← CheckpointBytes5Effect.read (parts state 2#u8)
 pure (blocks.set index block,advances.set index advance,advance)

def chain (state : Bytes32) : Code (Blocks × Blocks) := do
 let zero := Array.repeat 8#usize (Array.repeat 32#usize 0#u8)
 let (b0,a0,s0) ← pair 0#usize zero zero state
 let (b1,a1,s1) ← pair 1#usize b0 a0 s0
 let (b2,a2,s2) ← pair 2#usize b1 a1 s1
 let (b3,a3,s3) ← pair 3#usize b2 a2 s2
 let (b4,a4,s4) ← pair 4#usize b3 a3 s3
 let (b5,a5,s5) ← pair 5#usize b4 a4 s4
 let (b6,a6,s6) ← pair 6#usize b5 a5 s5
 let (b7,a7,s7) ← pair 7#usize b6 a6 s6
 pure (b7,a7)

/-- Only eight fixed array slots are normalized here. Digest replies are
symbolic32-byte arrays; no SHA, large numeral or recurrence is reduced. -/
theorem normalized (state : Bytes32) :
    NGQ_Normalize.normalize (NGQ_Effects.materializeCode state)=chain state := by
  rfl

/-- Full ordered attempt-log equality, including an unsuccessful call. -/
theorem run (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (state : Bytes32) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (chain state) before=
      SdkC_Source.run hashv (NGQ_Effects.materializeCode state) before := by
  rw [← normalized]
  exact NGQ_Normalize.run hashv _ before
#print axioms normalized
#print axioms run
end AspisR1.NGQ_MaterializeChain
end
