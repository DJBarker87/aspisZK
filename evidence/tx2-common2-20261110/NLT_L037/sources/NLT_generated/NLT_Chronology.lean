import NLT_C04NativeInstalled
set_option autoImplicit false
noncomputable section
namespace NLT_Chronology
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Histories come from the actual nested subcut at each occurrence. Aborting
subcuts are handled by their prefix law, not coerced to a completed history. -/
def history {H : Bytes → State} : {e : Event} → Detail H e → Option NLL.History
 | _,.ordinary _ _ => some []
 | _,.returning _ _ _ _ inside _ _ => some inside
 | _,.aborting .. => none
def completed {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} :
 List (Occurrence H d hash) → Option NLL.History
 | [] => some []
 | r::rs => do
   let inside←history r.detail
   let tail←completed rs
   some (inside++tail)
theorem prepend {H : Bytes → State} (e : Event) (detail : Detail H e)
 (rest : List Event) (tail inside : NLL.History) (native : NLP_C04Chronology.Native H rest tail)
 (returned : history detail=some inside) : NLP_C04Chronology.Native H (e::rest) (inside++tail) := by
 cases detail with
 | ordinary e notMerkle => cases returned;exact .skip e notMerkle rest tail native
 | returning pr p folded reply childHistory out child =>
   cases returned
   exact .merkle pr p folded reply childHistory out child rest tail native
 | aborting pr p folded error childHistory pending child => cases returned
theorem native {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (records : List (Occurrence H d hash)) (inside : NLL.History)
 (returned : completed records=some inside) : NLP_C04Chronology.Native H (records.map actual) inside := by
 induction records generalizing inside with
 | nil => cases returned;exact .nil
 | cons r rs ih =>
   cases hr : history r.detail with
   | none => simp only [completed,hr,Option.bind_none] at returned;cases returned
   | some first =>
     cases ht : completed rs with
     | none => simp only [completed,hr,ht,Option.bind_some,Option.bind_none] at returned;cases returned
     | some tail =>
       simp only [completed,hr,ht,Option.bind_some] at returned
       cases returned
       exact prepend (actual r) r.detail _ tail first (ih tail ht) hr
/-- Forward concatenation retains every occurrence and duplicate. The native
relation used here is DERIVED from the same parent records, not a new input. -/
theorem installed (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (root0 : NLP_InputDomain.Root0 ck proof) (result : R Unit) (records : List (Occurrence H d hash))
 (invocation : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (inside : NLL.History) (returned : completed records=some inside) :
 NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H) (records.map actual)=inside := by
 let f:=NLT_FrameFromCuts.frame records
 have joined:=NLT_NativeSource.source H d pub proof ck hash len result records invocation
 have packets : ∀ e∈records.map actual,NLP_C04All.Clause H e := by
  rw [joined.2]
  exact NLP_C04All.source H f.resume f.pending (NLP_NativeMerkle.action H)
   (NLB_Parent.finish f.finish) d pub proof ck hash len root0
 exact NLP_C04Chronology.fold H _ packets inside (native records inside returned)
set_option pp.proofs false
#print installed
#print axioms prepend
#print axioms native
#print axioms installed
end NLT_Chronology
