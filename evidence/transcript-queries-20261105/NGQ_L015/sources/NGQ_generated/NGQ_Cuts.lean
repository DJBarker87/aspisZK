import NGQ_Effects
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_Cuts
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect

/-- Local chronological edges. A producer must supply the SAME native trace;
this definition does not itself certify a Rust body. No whole Result/log equality
or successful execution is a constructor premise. -/
inductive Trace (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type} :
    Code A → Result A → SdkC_Source.Log → Prop where
 | done (a : A) : Trace hashv (.done a) (.ok a) []
 | stepOk {B : Type} (r : Result B) (k : B → Code A) (b : B)
     (edge : r=.ok b) (out : Result A) (events : SdkC_Source.Log)
     (tail : Trace hashv (k b) out events) : Trace hashv (.step r k) out events
 | stepFail {B : Type} (r : Result B) (k : B → Code A) (error : Error)
     (edge : r=.fail error) : Trace hashv (.step r k) (.fail error) []
 | stepDiv {B : Type} (r : Result B) (k : B → Code A)
     (edge : r=.div) : Trace hashv (.step r k) .div []
 | readOk (parts : SdkC_Source.Parts) (k : SdkC_Source.Digest → Code A)
     (reply : SdkC_Source.Digest) (edge : hashv parts=.ok reply)
     (out : Result A) (events : SdkC_Source.Log)
     (tail : Trace hashv (k reply) out events) :
     Trace hashv (.read parts k) out (⟨parts,.ok reply⟩::events)
 | readFail (parts : SdkC_Source.Parts) (k : SdkC_Source.Digest → Code A)
     (error : Error) (edge : hashv parts=.fail error) :
     Trace hashv (.read parts k) (.fail error) [⟨parts,.fail error⟩]
 | readDiv (parts : SdkC_Source.Parts) (k : SdkC_Source.Digest → Code A)
     (edge : hashv parts=.div) : Trace hashv (.read parts k) .div [⟨parts,.div⟩]

theorem run {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest} {A : Type}
    {code : Code A} {out : Result A} {events : SdkC_Source.Log}
    (trace : Trace hashv code out events) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv code before=(out,before++events) := by
  induction trace generalizing before with
  | done a => simp only [SdkC_Source.run,List.append_nil]
  | stepOk r k b edge out events tail ih =>
    simpa only [SdkC_Source.run,edge] using ih before
  | stepFail r k error edge => simp only [SdkC_Source.run,edge,List.append_nil]
  | stepDiv r k edge => simp only [SdkC_Source.run,edge,List.append_nil]
  | readOk parts k reply edge out events tail ih =>
    simp only [SdkC_Source.run,edge]
    rw [ih]
    simp only [List.append_assoc,List.singleton_append]
  | readFail parts k error edge => simp only [SdkC_Source.run,edge]
  | readDiv parts k edge => simp only [SdkC_Source.run,edge]

theorem association {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest} {A : Type}
    {code : Code A} (observed : NGP_L181.Observation A)
    (trace : Trace hashv code observed.result observed.attempted) :
    NGP_L181.NativeAssociation hashv code observed := by
  have h := run trace []
  simpa only [NGP_L181.NativeAssociation,List.nil_append] using h.symm
#print axioms run
#print axioms association
end AspisR1.NGQ_Cuts
end
