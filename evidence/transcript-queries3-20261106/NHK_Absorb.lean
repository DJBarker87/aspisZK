import NHK_EffectJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHK_Absorb
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation

def parts (self : transcript.Transcript Unit) (label : U8) (payload : Slice U8) : SdkC_Source.Parts :=
  Array.to_slice (Array.make 4#usize [Array.to_slice self.state,
    Array.to_slice (Array.make 2#usize [0#u8,label]),
    Array.to_slice (core.num.U32.to_le_bytes (UScalar.cast .U32 (Slice.len payload))),payload])

theorem normalized (self : transcript.Transcript Unit) (row label : U8) (payload : Slice U8)
    (tag : 160#u8 + row = ok label) :
    NGQ_Normalize.normalize (NGQ_Effects.absorbCode self row payload) =
      .read (parts self label payload) (fun reply => .done {self with state:=reply}) := by
  simp only [NGQ_Effects.absorbCode,Bind.bind,Pure.pure,CheckpointBytes5Effect.instMonadCode,
    CheckpointBytes5Effect.bind,liftResult,lift,NGQ_Normalize.normalize,tag]
  rfl

/-- These are local native call observations at the exact four descriptors,
not an assumed whole queries or absorb Result/log equality. -/
inductive Cut (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
    Result (transcript.Transcript Unit) → SdkC_Source.Log → Prop where
 | returned (label : U8) (reply : SdkC_Source.Digest)
     (tag : 160#u8 + row = ok label) (edge : hashv (parts self label payload)=ok reply) :
     Cut hashv self row payload (ok {self with state:=reply}) [⟨parts self label payload,ok reply⟩]
 | failed (label : U8) (error : Error)
     (tag : 160#u8 + row = ok label) (edge : hashv (parts self label payload)=.fail error) :
     Cut hashv self row payload (.fail error) [⟨parts self label payload,.fail error⟩]
 | diverged (label : U8)
     (tag : 160#u8 + row = ok label) (edge : hashv (parts self label payload)=.div) :
     Cut hashv self row payload .div [⟨parts self label payload,.div⟩]

theorem producer {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {self : transcript.Transcript Unit} {row : U8} {payload : Slice U8}
    {out : Result (transcript.Transcript Unit)} {events : SdkC_Source.Log}
    (cut : Cut hashv self row payload out events) :
    NGQ_Cuts.Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.absorbCode self row payload)) out events := by
  cases cut with
  | returned label reply tag edge =>
    rw [normalized self row label payload tag]
    exact .readOk _ _ reply edge _ _ (.done _)
  | failed label error tag edge =>
    rw [normalized self row label payload tag]
    exact .readFail _ _ error edge
  | diverged label tag edge =>
    rw [normalized self row label payload tag]
    exact .readDiv _ _ edge

/-- The native absorb packet's row domain is caller-established, with no
successful-digest premise. Payload<=8192 is retained by the native packet. -/
theorem tag_total (row : U8) (bound : row.val≤95) : ∃ label, 160#u8 + row=ok label := by
  have fits : (160#u8).val+row.val≤UScalar.max .U8 := by scalar_tac
  obtain ⟨label,call,_⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=160#u8) (y:=row) fits)
  exact ⟨label,call⟩

#print axioms normalized
#print axioms producer
#print axioms tag_total
end AspisR1.NHK_Absorb
end
