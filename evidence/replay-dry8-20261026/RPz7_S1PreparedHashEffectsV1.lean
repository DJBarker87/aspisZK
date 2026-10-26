import RPz7_S1PreparedSourceEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashEffects
open Aeneas Aeneas.Std Result
universe v

structure Effects (M : Type → Type v) where
  digest : {H : Type} → aspis_core.Digest32 H → H → Slice (Slice U8) → M (Array U8 32#usize)

def sourceEffects : Effects Result where digest := fun D hash parts => D.digest hash parts

def new {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) (hash : H)
  (semantic_state : Array Std.U8 32#usize) (variant : transport.Variant) :
  M (transcript.Transcript H)
  := do
  let domain ←
    lift (Array.to_slice
      (Array.make 29#usize [
        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
        49#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8, 84#u8, 69#u8, 45#u8,
        83#u8, 65#u8, 76#u8, 84#u8, 69#u8, 68#u8, 58#u8, 80#u8, 51#u8
        ]))
  let i ← transport.Variant.tag variant
  let s ← lift (Array.to_slice (Array.make 1#usize [ i ]))
  let s1 ← lift (Array.to_slice semantic_state)
  let s2 ← lift (Array.to_slice (Array.make 3#usize [ domain, s, s1 ]))
  let a ← effects.digest aspis_coreDigest32Inst hash s2
  pure { state := a, hash }

def absorb {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  M (transcript.Transcript H)
  := do
  let s ← lift (Array.to_slice self.state)
  let i ← 160#u8 + row
  let s1 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
  let i1 := Slice.len payload
  let i2 ← lift (UScalar.cast .U32 i1)
  let a ← lift (core.num.U32.to_le_bytes i2)
  let s2 ← lift (Array.to_slice a)
  let s3 ← lift (Array.to_slice (Array.make 4#usize [ s, s1, s2, payload ]))
  let a1 ← effects.digest aspis_coreDigest32Inst self.hash s3
  pure { self with state := a1 }

def block {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  M ((Array Std.U8 32#usize) × (transcript.Transcript H))
  := do
  let self1 ←
    absorb effects aspis_coreDigest32Inst self row payload
  let s ← lift (Array.to_slice self1.state)
  let s1 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  let block ← effects.digest aspis_coreDigest32Inst self1.hash s2
  let s3 ← lift (Array.to_slice self1.state)
  let s4 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
  let a ← effects.digest aspis_coreDigest32Inst self1.hash s5
  pure (block, { self1 with state := a })

theorem new_source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Array U8 32#usize) (variant : transport.Variant) :
    new sourceEffects D hash state variant=transcript.Transcript.new D hash state variant := rfl

theorem absorb_source {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    absorb sourceEffects D self row payload=transcript.Transcript.absorb D self row payload := rfl

theorem block_source {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    block sourceEffects D self row payload=transcript.Transcript.block D self row payload := rfl

#print axioms new_source
#print axioms absorb_source
#print axioms block_source
end AspisR1PublicPreparation.PreparedHashEffects
