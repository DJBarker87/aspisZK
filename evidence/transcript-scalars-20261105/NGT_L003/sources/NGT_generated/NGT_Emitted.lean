import NFQ_STAGE2_IMPORT
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_Emitted
open AspisR1PublicPreparation

/-- [aspis_r1_stage2_adopted_caller::transcript::{aspis_r1_stage2_adopted_caller::transcript::Transcript<H>}::absorb]:
    Source: 'lib.rs', lines 806:4-808:5
    Visibility: public -/
def absorb
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Result (transcript.Transcript H)
  := do
  let s ← lift (Array.to_slice self.state)
  let i ← 160#u8 + row
  let s1 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
  let i1 := Slice.len payload
  let i2 ← lift (UScalar.cast .U32 i1)
  let a ← lift (core.num.U32.to_le_bytes i2)
  let s2 ← lift (Array.to_slice a)
  let s3 ← lift (Array.to_slice (Array.make 4#usize [ s, s1, s2, payload ]))
  let a1 ← aspis_coreDigest32Inst.digest self.hash s3
  ok { self with state := a1 }

/-- [aspis_r1_stage2_adopted_caller::transcript::{aspis_r1_stage2_adopted_caller::transcript::Transcript<H>}::block]:
    Source: 'lib.rs', lines 809:4-814:5
    Visibility: public -/
def block
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Result ((Array Std.U8 32#usize) × (transcript.Transcript H))
  := do
  let self1 ←
    absorb aspis_coreDigest32Inst self row payload
  let s ← lift (Array.to_slice self1.state)
  let s1 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  let block ← aspis_coreDigest32Inst.digest self1.hash s2
  let s3 ← lift (Array.to_slice self1.state)
  let s4 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
  let a ← aspis_coreDigest32Inst.digest self1.hash s5
  ok (block, { self1 with state := a })

/-- [aspis_r1_stage2_adopted_caller::transcript::{aspis_r1_stage2_adopted_caller::transcript::Transcript<H>}::scalar]:
    Source: 'lib.rs', lines 786:4-790:5
    Visibility: public -/
def scalar
  (B : PreparedModel.Boundaries)   {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) :
  Result (aspis_core.field.WideExact × (transcript.Transcript H))
  := do
  let (block, self1) ←
    block aspis_coreDigest32Inst self row payload
  let out ←
    if nonzero
    then B.gamma block
    else B.ordinary block
  let i ← lift (UScalar.cast .Usize row)
  trace.value 4#u16 i out
  ok (out, self1)

/-- [aspis_r1_stage2_adopted_caller::transcript::{aspis_r1_stage2_adopted_caller::transcript::Transcript<H>}::scalar_k]:
    Source: 'lib.rs', lines 794:4-797:5
    Visibility: public -/
def scalar_k
  (B : PreparedModel.Boundaries)   {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Result (aspis_core.field.QM31 × (transcript.Transcript H))
  := do
  let (a, self1) ←
    block aspis_coreDigest32Inst self row payload
  let out ← sampler.qm31_sample a
  let i ← lift (UScalar.cast .Usize row)
  let we ← B.fromQm out
  trace.value 4#u16 i we
  ok (out, self1)

end AspisR1.NGT_Emitted
