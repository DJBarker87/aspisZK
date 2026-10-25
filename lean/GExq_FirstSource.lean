import GExq_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_FirstSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect
open GExp_FirstCode GExq_FirstCode GExq_FirstErasure
local instance : MonadLift Result Code where monadLift := liftResult

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)

theorem source {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (law : ∀ h parts, D.digest h parts = hashv parts)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    erase (SdkC_Source.dictionary hashv) () (GExq_FirstCode.code base B std hashv D semantic pub proof split hash) =
      verifier.candidate.tx1 (installed base B std) D semantic pub proof split hash none := by
  simp only [GExq_FirstCode.code,verifier.candidate.tx1,erase_bind,GExp_FirstErasure.erase_liftM,erase_pure,
    prepare base B std hashv D law,batch hashv D hash (law hash),writer hashv D hash (law hash)]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,GExp_FirstErasure.erase_liftM,erase_pure,
        prepare base B std hashv D law,batch hashv D hash (law hash),writer hashv D hash (law hash)])
    | (apply bind_congr; intro x)
    | split

#print axioms bind_congr
#print axioms source
end AspisR1.GExq_FirstSource
end
