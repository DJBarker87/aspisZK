import RPz7_GExp_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FirstSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect
open GExp_FirstCode GExp_FirstErasure
local instance : MonadLift Result Code where monadLift := liftResult

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)

theorem source (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    erase (SdkC_Source.dictionary hashv) () (code base B std hashv D semantic pub proof split) =
      verifier.candidate.tx1 (installed base B std) D semantic pub proof split () none := by
  simp only [code,verifier.candidate.tx1,erase_bind,erase_liftM,erase_pure,
    prepare base B std hashv D law,batch hashv D law,writer hashv D law]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_liftM,erase_pure,
        prepare base B std hashv D law,batch hashv D law,writer hashv D law])
    | (apply bind_congr; intro x)
    | split

#print axioms bind_congr
#print axioms source
end AspisR1.GExp_FirstSource
end
