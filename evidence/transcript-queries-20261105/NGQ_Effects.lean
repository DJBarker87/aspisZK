import NGQ_Embed
import NGP_OracleTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_Effects
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open CheckpointBytes5Effect
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize
abbrev Reply := core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript Unit

def dictionary (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : aspis_core.Digest32 Unit where
 coremarkerCopyInst := {cloneInst := {clone := fun q => ok q}}
 digest := fun _ parts => hashv parts

def dummy : aspis_core.Digest32 Unit := dictionary (fun _ => .div)

def materializeCode (state0 : Bytes32) : Code (Blocks × Blocks) := do
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← liftResult (lift (Array.to_slice state0))
  let s1 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s2 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s, s1 ])))
  let a1 ← CheckpointBytes5Effect.read s2
  let (_, index_mut_back) ← liftResult (Array.index_mut_usize blocks 0#usize)
  let s3 ← liftResult (lift (Array.to_slice state0))
  let s4 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s5 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s3, s4 ])))
  let a2 ← CheckpointBytes5Effect.read s5
  let blocks1 := index_mut_back a2
  let state ← liftResult (Array.index_usize blocks1 0#usize)
  let s6 ← liftResult (lift (Array.to_slice state))
  let s7 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s8 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s6, s7 ])))
  let a3 ← CheckpointBytes5Effect.read s8
  let blocks2 := index_mut_back a1
  let blocks3 ← liftResult (Array.update blocks2 1#usize a3)
  let s9 ← liftResult (lift (Array.to_slice state))
  let s10 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s11 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s9, s10 ])))
  let a4 ← CheckpointBytes5Effect.read s11
  let blocks4 ← liftResult (Array.update blocks1 1#usize a4)
  let state1 ← liftResult (Array.index_usize blocks4 1#usize)
  let s12 ← liftResult (lift (Array.to_slice state1))
  let s13 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s14 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s12, s13 ])))
  let a5 ← CheckpointBytes5Effect.read s14
  let blocks5 ← liftResult (Array.update blocks3 2#usize a5)
  let s15 ← liftResult (lift (Array.to_slice state1))
  let s16 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s17 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s15, s16 ])))
  let a6 ← CheckpointBytes5Effect.read s17
  let blocks6 ← liftResult (Array.update blocks4 2#usize a6)
  let state2 ← liftResult (Array.index_usize blocks6 2#usize)
  let s18 ← liftResult (lift (Array.to_slice state2))
  let s19 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s20 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s18, s19 ])))
  let a7 ← CheckpointBytes5Effect.read s20
  let blocks7 ← liftResult (Array.update blocks5 3#usize a7)
  let s21 ← liftResult (lift (Array.to_slice state2))
  let s22 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s23 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s21, s22 ])))
  let a8 ← CheckpointBytes5Effect.read s23
  let blocks8 ← liftResult (Array.update blocks6 3#usize a8)
  let state3 ← liftResult (Array.index_usize blocks8 3#usize)
  let s24 ← liftResult (lift (Array.to_slice state3))
  let s25 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s26 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s24, s25 ])))
  let a9 ← CheckpointBytes5Effect.read s26
  let blocks9 ← liftResult (Array.update blocks7 4#usize a9)
  let s27 ← liftResult (lift (Array.to_slice state3))
  let s28 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s29 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s27, s28 ])))
  let a10 ← CheckpointBytes5Effect.read s29
  let blocks10 ← liftResult (Array.update blocks8 4#usize a10)
  let state4 ← liftResult (Array.index_usize blocks10 4#usize)
  let s30 ← liftResult (lift (Array.to_slice state4))
  let s31 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s32 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s30, s31 ])))
  let a11 ← CheckpointBytes5Effect.read s32
  let blocks11 ← liftResult (Array.update blocks9 5#usize a11)
  let s33 ← liftResult (lift (Array.to_slice state4))
  let s34 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s35 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s33, s34 ])))
  let a12 ← CheckpointBytes5Effect.read s35
  let blocks12 ← liftResult (Array.update blocks10 5#usize a12)
  let state5 ← liftResult (Array.index_usize blocks12 5#usize)
  let s36 ← liftResult (lift (Array.to_slice state5))
  let s37 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s38 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s36, s37 ])))
  let a13 ← CheckpointBytes5Effect.read s38
  let blocks13 ← liftResult (Array.update blocks11 6#usize a13)
  let s39 ← liftResult (lift (Array.to_slice state5))
  let s40 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s41 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s39, s40 ])))
  let a14 ← CheckpointBytes5Effect.read s41
  let blocks14 ← liftResult (Array.update blocks12 6#usize a14)
  let state6 ← liftResult (Array.index_usize blocks14 6#usize)
  let s42 ← liftResult (lift (Array.to_slice state6))
  let s43 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s44 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s42, s43 ])))
  let a15 ← CheckpointBytes5Effect.read s44
  let blocks15 ← liftResult (Array.update blocks13 7#usize a15)
  let s45 ← liftResult (lift (Array.to_slice state6))
  let s46 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s47 ← liftResult (lift (Array.to_slice (Array.make 2#usize [ s45, s46 ])))
  let a16 ← CheckpointBytes5Effect.read s47
  let blocks16 ← liftResult (Array.update blocks14 7#usize a16)
  let _ ← liftResult (Array.index_usize blocks16 7#usize)
  pure (blocks15, blocks16)

/-- Reification records each digest occurrence once, preserving the emitted
pure operations and their failures. This is a model theorem, not native credit. -/
theorem materialize_erasure (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (state : Bytes32) :
    erase (SdkC_Source.dictionary hashv) () (materializeCode state)=
      NGQ_QueryFactor.materialize (dictionary hashv) () state := by
  simp only [materializeCode,erase_bind,erase_lift,erase_read,erase_pure,
    NGQ_QueryFactor.materialize,dictionary,SdkC_Source.dictionary]
  rfl

def absorbCode (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
    Code (transcript.Transcript Unit) := do
  let s ← liftResult (lift (Array.to_slice self.state))
  let i ← liftResult (160#u8 + row)
  let s1 ← liftResult (lift (Array.to_slice (Array.make 2#usize [0#u8,i])))
  let i2 ← liftResult (lift (UScalar.cast .U32 (Slice.len payload)))
  let a ← liftResult (lift (core.num.U32.to_le_bytes i2))
  let s2 ← liftResult (lift (Array.to_slice a))
  let s3 ← liftResult (lift (Array.to_slice (Array.make 4#usize [s,s1,s2,payload])))
  let a1 ← CheckpointBytes5Effect.read s3
  pure {self with state:=a1}

theorem absorb_erasure (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
    erase (SdkC_Source.dictionary hashv) () (absorbCode self row payload)=
      transcript.Transcript.absorb (dictionary hashv) self row payload := by
  simp only [absorbCode,erase_bind,erase_lift,erase_read,erase_pure,
    transcript.Transcript.absorb,dictionary,SdkC_Source.dictionary]

/-- The map-error closure is independent of the digest dictionary. -/
theorem tail_dictionary (B : QueriesModel.Boundaries) (D D' : aspis_core.Digest32 Unit)
    (self : transcript.Transcript Unit) (blocks advances : Blocks) :
    NGQ_QueryFactor.finishQuery B D self blocks advances=
      NGQ_QueryFactor.finishQuery B D' self blocks advances := by
  rfl

def code (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) : Code Reply := do
  let absorbed ← absorbCode self row payload
  let (blocks,advances) ← materializeCode absorbed.state
  liftResult (NGQ_QueryFactor.finishQuery B dummy absorbed blocks advances)

theorem factor_tail (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 Unit)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
    NGQ_QueryFactor.queriesFactored B D self row payload =
      (do let absorbed ← transcript.Transcript.absorb D self row payload
          let (blocks,advances) ← NGQ_QueryFactor.materialize D absorbed.hash absorbed.state
          NGQ_QueryFactor.finishQuery B D absorbed blocks advances) := by rfl

/-- Full Result equality, including sampler rejection and every pure failure.
Ordered syscall events are retained by SdkC_Source.run, rather than inferred
from equality of Results. SAME inputs and boundaries occur on both sides. -/
theorem model_result (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) :
    (SdkC_Source.run hashv (code B self row payload) []).1 =
      QueriesModel.queries B (dictionary hashv) self row payload := by
  rw [SdkC_Source.erasure,NGQ_QueryJoin.source,factor_tail]
  simp only [code,erase_bind,erase_lift,absorb_erasure,materialize_erasure,
    tail_dictionary B dummy (dictionary hashv)]
  cases self with
  | mk state hash => cases hash; rfl

#print axioms materialize_erasure
#print axioms absorb_erasure
#print axioms tail_dictionary
#print axioms factor_tail
#print axioms model_result
end AspisR1.NGQ_Effects
end
