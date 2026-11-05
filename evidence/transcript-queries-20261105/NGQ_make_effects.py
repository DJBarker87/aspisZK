"""Reify only digest occurrences; every other emitted primitive stays a Result step."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;src=(E/'NGQ_QueryFactor.lean').read_text();a=src.index('  let a := Array.repeat');b=src.index('\ndef queriesFactored',a);body=src[a:b].strip('\n')
rows=[]
for line in body.splitlines():
 m=re.fullmatch(r'(  let .*? ← )(.*)',line)
 if m:
  expr=m[2]
  if 'aspis_coreDigest32Inst.digest hash ' in expr:
   line=m[1]+'CheckpointBytes5Effect.read '+expr.split('aspis_coreDigest32Inst.digest hash ')[1]
  else:line=m[1]+'liftResult ('+expr+')'
 elif line.startswith('  ok '):line=line.replace('  ok ','  pure ',1)
 rows.append(line)
translated='\n'.join(rows)
s='''import NGQ_Embed
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
'''+translated+'''

/-- Reification records each digest occurrence once, preserving the emitted
pure operations and their failures. This is a model theorem, not native credit. -/
theorem materialize_erasure (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (state : Bytes32) :
    erase (SdkC_Source.dictionary hashv) () (materializeCode state)=
      NGQ_QueryFactor.materialize (dictionary hashv) () state := by
  simp only [materializeCode,erase_bind,erase_lift,erase_read,erase_pure,
    NGQ_QueryFactor.materialize,dictionary,SdkC_Source.dictionary]\n  rfl

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
'''
(E/'NGQ_Effects.lean').write_text(s)
(E/'NGQ_EFFECT_REIFICATION.json').write_text(json.dumps(dict(input='NGQ_QueryFactor.lean',input_sha256=hashlib.sha256(src.encode()).hexdigest(),materialize_digest_occurrences=body.count('aspis_coreDigest32Inst.digest hash '),output_digest_reads=translated.count('CheckpointBytes5Effect.read'),pure_bindings=translated.count('liftResult ('),rule='Only digest binds become read; other Result binds become liftResult; pure lets unchanged'),indent=1)+'\n')
