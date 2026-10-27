import GExq_CodeTrace
import RawK_PrepareHead
import GExp_LowerTrace
import GExq_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_CodeHead
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisR1CurrentCaller

def head {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (p : Code A) :=
  (SdkC_Source.readLog (SdkC_Source.run hashv p []).2).head?

theorem lift_empty {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (r : Result A) :
    SdkC_Source.readLog (SdkC_Source.run hashv (liftResult r) []).2 = [] := by
  cases r <;> rfl

theorem right {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (k : A → Code B) (out : B)
    (success : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Effect.bind p k) = ok out)
    (empty : SdkC_Source.readLog (SdkC_Source.run hashv p []).2 = [] := by apply AspisR1.RawK_CodeHead.lift_empty) :
    ∃ a, erase (SdkC_Source.dictionary hashv) () p = ok a ∧
      erase (SdkC_Source.dictionary hashv) () (k a) = ok out ∧
      ∀ entry, head hashv (k a) = some entry → head hashv (CheckpointBytes5Effect.bind p k) = some entry := by
  obtain ⟨a,hp,hk,logs⟩ := GExq_CodeTrace.success_bind hashv _ _ _ success
  refine ⟨a,hp,hk,?_⟩
  intro entry h
  simpa only [head,logs,empty,List.nil_append] using h

theorem left {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (k : A → Code B) (out : B)
    (success : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Effect.bind p k) = ok out) :
    ∀ entry, head hashv p = some entry → head hashv (CheckpointBytes5Effect.bind p k) = some entry := by
  obtain ⟨a,hp,hk,logs⟩ := GExq_CodeTrace.success_bind hashv _ _ _ success
  intro entry h
  simp only [head,logs]
  cases observed : SdkC_Source.readLog (SdkC_Source.run hashv p []).2 with
  | nil => simp only [head,observed,List.head?_nil] at h; cases h
  | cons first rest => simpa only [head,observed,List.cons_append,List.head?_cons] using h

theorem prepare {Hash : Type} (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (source : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8) (hash : Hash)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : erase (SdkC_Source.dictionary hashv) () (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input)) = ok (.Ok p,scratch)) :
    ∃ entry, head hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input)) = some entry ∧
      entry.1.head? = some 85 := by
  have association := GExp_PrepareAssociation.prepare ops AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub proof hash input hashv source
  have logs := GExp_LowerTrace.log hashv (SdkD_PrepareSource.code ops B std D pub proof hash input) association
  have erased := (SdkD_PrepareLower.erasure hashv
    (SdkD_PrepareSource.code ops B std D pub proof hash input) association).symm.trans success
  change AspisR1PublicPreparation.PreparedHashCode.erase
    (S1PrepareCode.prepare ops AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub proof hash input) = _ at erased
  obtain ⟨entry,h,tag⟩ := RawK_PrepareHead.reached _ _ _ D pub proof hash p input scratch erased
  exact ⟨entry,by simpa only [head,logs,RawK_Head.head,SdkD_PrepareSource.code] using h,tag⟩

#print axioms lift_empty
#print axioms right
#print axioms left
#print axioms prepare
end AspisR1.RawK_CodeHead
end
