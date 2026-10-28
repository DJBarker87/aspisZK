import NBL_CodeRunLaws
import NBL_BlockTrace
set_option autoImplicit false
namespace AspisR1.NBL_HashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws
abbrev Bytes32 := Array U8 32#usize

def events {H : Type} (D : aspis_core.Digest32 H) (hash : H) (log : NBL_BlockTrace.Log) : Log :=
  log.map (fun event => Event.digest D hash event.1 (ok event.2))

/-- Typed attempted-log replay of the actual existing hash-effects absorb. -/
theorem absorb {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row tag : U8) (payload : Slice U8) (reply : Bytes32)
    (tagCall : (160#u8+row : Result U8)=ok tag)
    (call : D.digest before.hash (NBA_Transcript.absorbParts before.state tag payload)=ok reply) :
    run (PreparedHashEffects.absorb effects D before row payload)=
      ([Event.digest D before.hash (NBA_Transcript.absorbParts before.state tag payload) (ok reply)],
        ok ({before with state:=reply} : transcript.Transcript H)) := by
  have call' := call
  simp only [NBA_Transcript.absorbParts] at call'
  simp only [PreparedHashEffects.absorb,bind_run,lift_run,pure_run,digest_run,
    chain,lift,tagCall,call',NBA_Transcript.absorbParts,List.nil_append,List.append_nil]

/-- All three typed hash attempts and the returned state, on the SAME replies. -/
theorem block {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (b : NBL_BlockTrace.Block D before row payload) :
    run (PreparedHashEffects.block effects D before row payload)=
      (events D before.hash b.log,ok (b.value,b.after)) := by
  have first := absorb D before row b.tag payload b.absorbed b.tagCall b.absorbCall
  have second := b.readCall
  have third := b.advanceCall
  simp only [NBA_Transcript.readParts] at second third
  simp only [PreparedHashEffects.block,bind_run,first,chain,lift_run,pure_run,digest_run,
    lift,second,third,events,NBL_BlockTrace.Block.log,NBL_BlockTrace.Block.after,
    NBA_Transcript.readParts,List.map_cons,List.map_nil,List.nil_append,List.append_nil]

/-- Salted S2 seed event; no independently chosen starting transcript. -/
theorem seed {H : Type} (D : aspis_core.Digest32 H) (hash : H) (state reply : Bytes32)
    (call : D.digest hash (NBA_Transcript.seedParts state)=ok reply) :
    run (PreparedHashEffects.new effects D hash state .S2)=
      ([Event.digest D hash (NBA_Transcript.seedParts state) (ok reply)],
        ok (⟨reply,hash⟩ : transcript.Transcript H)) := by
  have call' := call
  simp only [NBA_Transcript.seedParts,NBA_Transcript.domain] at call'
  simp only [PreparedHashEffects.new,transport.Variant.tag,bind_run,lift_run,pure_run,digest_run,
    chain,lift,call',NBA_Transcript.seedParts,NBA_Transcript.domain,List.nil_append,List.append_nil]

#print axioms absorb
#print axioms block
#print axioms seed
end AspisR1.NBL_HashReplay
