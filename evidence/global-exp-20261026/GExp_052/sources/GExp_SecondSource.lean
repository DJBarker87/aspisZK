import GExp_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_SecondSource
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect
open GExp_SecondCode
local instance : MonadLift Result Code where monadLift := liftResult

theorem erase_liftM {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : Result A) : erase (SdkC_Source.dictionary hashv) () (monadLift r : Code A) = r :=
  erase_lift _ _ r

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)

theorem batch (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) :
    erase (SdkC_Source.dictionary hashv) () (SdkC_BatchSource.stageCode hashv proof p root) =
    Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize () := by
  rw [← SdkC_Source.erasure hashv _ []]
  exact SdkC_BatchSource.stage_source hashv D law proof p root []

theorem common_source (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (pub proof ck : Slice U8) :
    erase (SdkC_Source.dictionary hashv) () (common base reserved hashv D pub proof ck) =
      verifier.candidate.tx2_common (installed base reserved) D pub proof ck () none := by
  simp only [common,verifier.candidate.tx2_common,erase_bind,erase_liftM,erase_pure,
    GExp_RetainedReader.source reserved hashv D law,batch hashv D law]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_liftM,erase_pure,
        GExp_RetainedReader.source reserved hashv D law,batch hashv D law])
    | (apply bind_congr; intro x)
    | split

theorem source (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (pub proof ck : Slice U8) :
    erase (SdkC_Source.dictionary hashv) () (code base reserved hashv D pub proof ck) =
      verifier.candidate.tx2_authenticated (installed base reserved) D pub proof ck () none := by
  simp only [code,verifier.candidate.tx2_authenticated,erase_bind,erase_liftM,erase_pure,
    common_source base reserved hashv D law]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_liftM,erase_pure,
        common_source base reserved hashv D law])
    | (apply bind_congr; intro x)
    | split

#print axioms erase_liftM
#print axioms bind_congr
#print axioms batch
#print axioms common_source
#print axioms source
end AspisR1.GExp_SecondSource
end
