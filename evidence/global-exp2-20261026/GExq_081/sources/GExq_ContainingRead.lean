import GExq_CodeTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_ContainingRead
open Aeneas Aeneas.Std Result GExq_OuterLower CheckpointBytes5Effect
open FS2.Duplex

def Reads {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (code : Code A)
    (frame : AspisV8R19.DuplexFrames.Bytes) :=
  Read (SdkC_Source.readLog (SdkC_Source.run hashv code []).2) frame

def eventReads (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {A : Type} → S2W_Trace.Call A → Oracle A) :
    S2W_Trace.Event → (AspisV8R19.DuplexFrames.Bytes → Prop)
  | .returned call _ => Reads hashv (impl call)

theorem containing {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) (before after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run sdk code before = ok (value,after))
    (event : S2W_Trace.Event) (member : event ∈ after) :
    event ∈ before ∨ ∀ frame, eventReads hashv impl event frame → Reads hashv (lower impl code) frame := by
  induction code generalizing before after with
  | done a => exact Or.inl (by cases Result.ok.inj ran; exact member)
  | step r k ih =>
    cases r with
    | fail e => cases ran
    | div => cases ran
    | ok a => exact ih a good before after ran member
  | call op k ih =>
    cases actual : S2W_Trace.invoke sdk op with
    | fail e => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | div => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | ok a =>
      have erased : S2W_Trace.erase sdk (.call op k) = ok value := by
        rw [← S2W_Trace.erase_run sdk (.call op k) before,ran]
        rfl
      have total := (GExq_OuterLower.erasure sdk hashv impl law (.call op k) good).trans erased
      have called := (law op good.1).trans actual
      simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran
      rcases ih a (good.2 a) (before ++ [.returned op a]) after ran member with old | fresh
      · rcases List.mem_append.mp old with old | same
        · exact Or.inl old
        · obtain rfl := List.mem_singleton.mp same
          right
          intro frame read
          exact GExq_CodeTrace.left_read hashv (impl op) (fun b => lower impl (k b)) value total frame read
      · right
        intro frame read
        obtain ⟨chosen,hchosen,_,include⟩ := GExq_CodeTrace.right_read hashv (impl op)
          (fun b => lower impl (k b)) value total
        have same : chosen = a := Result.ok.inj (hchosen.symm.trans called)
        subst chosen
        exact include frame (fresh frame read)

theorem from_empty {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) (after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run sdk code [] = ok (value,after))
    (event : S2W_Trace.Event) (member : event ∈ after) :
    ∀ frame, eventReads hashv impl event frame → Reads hashv (lower impl code) frame := by
  rcases containing sdk hashv impl law code good [] after value ran event member with empty | present
  · cases empty
  · exact present

#print axioms containing
#print axioms from_empty
end AspisR1.GExq_ContainingRead
end
