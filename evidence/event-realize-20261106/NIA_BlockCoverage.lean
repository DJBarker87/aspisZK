import NIA_ScalarFailures
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_BlockCoverage
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIA_ScalarFailures

/-- No non-success partial-dictionary branch is excluded from the block packet.
No whole block equation, packet, or successful run is a premise. The physical
identification of this partial dictionary remains a separate native obligation. -/
theorem complete (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
 Nonempty (NGT_NBL_BlockTrace.Block (NGQ_Effects.dictionary hashv) before row payload) ∨
 ∃ stop events, BlockStop hashv before row payload stop events := by
 cases tagCall : (160#u8+row : Result U8) with
 | fail e => exact Or.inr ⟨.fail e,[],.tag (.fail e) tagCall⟩
 | div => exact Or.inr ⟨.div,[],.tag .div tagCall⟩
 | ok tag =>
   cases first : hashv (NGT_NBA_Transcript.absorbParts before.state tag payload) with
   | fail e => exact Or.inr ⟨.fail e,_,.absorb (.fail e) tag tagCall first⟩
   | div => exact Or.inr ⟨.div,_,.absorb .div tag tagCall first⟩
   | ok absorbed =>
     cases second : hashv (NGT_NBA_Transcript.readParts absorbed 1#u8) with
     | fail e => exact Or.inr ⟨.fail e,_,.read (.fail e) tag absorbed tagCall first second⟩
     | div => exact Or.inr ⟨.div,_,.read .div tag absorbed tagCall first second⟩
     | ok value =>
       cases third : hashv (NGT_NBA_Transcript.readParts absorbed 2#u8) with
       | fail e => exact Or.inr ⟨.fail e,_,.advance (.fail e) tag absorbed value tagCall first second third⟩
       | div => exact Or.inr ⟨.div,_,.advance .div tag absorbed value tagCall first second third⟩
       | ok final => exact Or.inl ⟨⟨tag,tagCall,absorbed,value,final,first,second,third⟩⟩

/-- Every stopped prefix has at most the three actual calls. -/
theorem length {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
 {before : transcript.Transcript Unit} {row : U8} {payload : Slice U8}
 {stop : Stop} {events : SdkC_Source.Log}
 (packet : BlockStop hashv before row payload stop events) : events.length≤3 := by
 cases packet <;> simp only [List.length_cons,List.length_nil] <;> omega

/-- A failed block result yields a packet on the SAME invocation. -/
theorem failed (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8) (error : Error)
 (returned : transcript.Transcript.block (NGQ_Effects.dictionary hashv) before row payload=.fail error) :
 ∃ events, BlockStop hashv before row payload (.fail error) events := by
 rcases complete hashv before row payload with success | ⟨stop,events,packet⟩
 · obtain ⟨b⟩ := success
   have same := (NGT_NBL_BlockTrace.block_result _ _ _ _ b).symm.trans returned
   cases same
 · have same := (block_result packet).symm.trans returned
   cases stop with
   | fail e => cases same; exact ⟨events,packet⟩
   | div => cases same

theorem diverged (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
 (returned : transcript.Transcript.block (NGQ_Effects.dictionary hashv) before row payload=.div) :
 ∃ events, BlockStop hashv before row payload .div events := by
 rcases complete hashv before row payload with success | ⟨stop,events,packet⟩
 · obtain ⟨b⟩ := success
   have same := (NGT_NBL_BlockTrace.block_result _ _ _ _ b).symm.trans returned
   cases same
 · have same := (block_result packet).symm.trans returned
   cases stop with
   | fail e => cases same
   | div => exact ⟨events,packet⟩

#print axioms complete
#print axioms length
#print axioms failed
#print axioms diverged
end AspisR1.NIA_BlockCoverage
