import NHK_Absorb
import NHK_NativeBlocks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHK_Invocation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Blocks := NGQ_Effects.Blocks
abbrev SamplerOut := NGQ_SamplerDriver.Out

/-- Actual caller domain of the retained absorb native certificate. -/
structure Domain (row : U8) (payload : Slice U8) : Prop where
  rowBound : row.val≤95
  payloadBound : payload.val.length≤8192

def tailReply (absorbed : transcript.Transcript Unit) : SamplerOut → NGQ_Effects.Reply
 | .Ok (q,state) => (.Ok q,{absorbed with state:=state})
 | .Err _ => (.Err .Transcript,absorbed)

theorem tail_source (absorbed : transcript.Transcript Unit) (blocks advances : Blocks)
    (out : SamplerOut)
    (cuts : NHK_NativeBlocks.Cuts advances
      (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
      NGQ_SamplerPacket.initial out) :
    NGQ_QueryFactor.finishQuery NGQ_TRANSCRIPT.boundaries NGQ_Effects.dummy absorbed blocks advances =
      ok (tailReply absorbed out) := by
  have decode := (NHK_NativeBlocks.sampler blocks advances out cuts).1
  cases out with
  | Ok value =>
    rcases value with ⟨q,state⟩
    exact NGQ_Embed.finish NGQ_Effects.dummy absorbed NGQ_SamplerPacket.decode blocks advances q state decode
  | Err error =>
    exact NGQ_TraceErase.finish_rejected NGQ_TRANSCRIPT.boundaries NGQ_Effects.dummy absorbed blocks advances
      (NGQ_SamplerPacket.errorPort error) decode

/-- Same-invocation source-order cuts. The observed result/log is constructed
from the actual local replies and events; no whole Result/log equality and no
complete NGQ_Cuts.Trace occurs as a constructor premise. -/
inductive Cuts (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
    NGP_L181.Observation NGQ_Effects.Reply → Prop where
 | absorbFail (events : SdkC_Source.Log) (error : Error)
     (cut : NHK_Absorb.Cut hashv self row payload (.fail error) events) :
     Cuts hashv self row payload ⟨.fail error,events⟩
 | absorbDiv (events : SdkC_Source.Log)
     (cut : NHK_Absorb.Cut hashv self row payload .div events) :
     Cuts hashv self row payload ⟨.div,events⟩
 | pairsFail (absorbed : transcript.Transcript Unit) (absorbEvents pairEvents : SdkC_Source.Log)
     (error : Error)
     (absorbCut : NHK_Absorb.Cut hashv self row payload (.ok absorbed) absorbEvents)
     (pairCuts : NHK_EventChain.PartialObservations hashv
       [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
       (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
       (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) absorbed.state (.fail error) pairEvents) :
     Cuts hashv self row payload ⟨.fail error,absorbEvents++pairEvents⟩
 | pairsDiv (absorbed : transcript.Transcript Unit) (absorbEvents pairEvents : SdkC_Source.Log)
     (absorbCut : NHK_Absorb.Cut hashv self row payload (.ok absorbed) absorbEvents)
     (pairCuts : NHK_EventChain.PartialObservations hashv
       [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
       (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
       (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) absorbed.state .div pairEvents) :
     Cuts hashv self row payload ⟨.div,absorbEvents++pairEvents⟩
 | returning (absorbed : transcript.Transcript Unit) (absorbEvents pairEvents : SdkC_Source.Log)
     (blocks advances : Blocks) (samplerOut : SamplerOut)
     (absorbCut : NHK_Absorb.Cut hashv self row payload (.ok absorbed) absorbEvents)
     (pairCuts : NHK_EventChain.PartialObservations hashv
       [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
       (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
       (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) absorbed.state (.ok (blocks,advances)) pairEvents)
     (samplerCuts : NHK_NativeBlocks.Cuts advances
       (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
       NGQ_SamplerPacket.initial samplerOut) :
     Cuts hashv self row payload ⟨.ok (tailReply absorbed samplerOut),absorbEvents++pairEvents⟩

/-- The producer assembles the SAME cut fields, including failed/diverging
syscalls and pure sampler rejection. This is not a trace chosen by model run. -/
theorem producer {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {self : transcript.Transcript Unit} {row : U8} {payload : Slice U8}
    {observed : NGP_L181.Observation NGQ_Effects.Reply}
    (cuts : Cuts hashv self row payload observed) :
    NGQ_Cuts.Trace hashv
      (NGQ_Normalize.normalize (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload))
      observed.result observed.attempted := by
  cases cuts with
  | absorbFail events error cut =>
    exact NHK_EffectJoin.absorb_fail hashv NGQ_TRANSCRIPT.boundaries self row payload events error
      (NHK_Absorb.producer cut)
  | absorbDiv events cut =>
    exact NHK_EffectJoin.absorb_div hashv NGQ_TRANSCRIPT.boundaries self row payload events
      (NHK_Absorb.producer cut)
  | pairsFail absorbed absorbEvents pairEvents error absorbCut pairCuts =>
    exact NHK_EffectJoin.returning_absorb hashv NGQ_TRANSCRIPT.boundaries self absorbed row payload
      absorbEvents pairEvents (.fail error) (.fail error) (NHK_Absorb.producer absorbCut) pairCuts rfl
  | pairsDiv absorbed absorbEvents pairEvents absorbCut pairCuts =>
    exact NHK_EffectJoin.returning_absorb hashv NGQ_TRANSCRIPT.boundaries self absorbed row payload
      absorbEvents pairEvents .div .div (NHK_Absorb.producer absorbCut) pairCuts rfl
  | returning absorbed absorbEvents pairEvents blocks advances samplerOut absorbCut pairCuts samplerCuts =>
    exact NHK_EffectJoin.returning_absorb hashv NGQ_TRANSCRIPT.boundaries self absorbed row payload
      absorbEvents pairEvents (.ok (blocks,advances)) (.ok (tailReply absorbed samplerOut))
      (NHK_Absorb.producer absorbCut) pairCuts (tail_source absorbed blocks advances samplerOut samplerCuts)

#print axioms tail_source
#print axioms producer
end AspisR1.NHK_Invocation
end
