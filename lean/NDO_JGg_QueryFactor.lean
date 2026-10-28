import NDO_JGg_QuerySplit
set_option autoImplicit false
namespace AspisR1.JGg_QueryFactor
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open JGg_QuerySplit

theorem bind_tail {A B : Type} (m : Result A) (f g : A → Result B)
    (same : ∀ x,f x=g x) : (m >>= f)=(m >>= g) :=
  congrArg (fun k => m >>= k) (funext same)
#print axioms bind_tail

theorem source_eq {Hash : Type} (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (self : transcript.Transcript Hash) (row : U8) (payload : Slice U8) :
    QueriesModel.queries B D self row payload=initial D self row payload (finish B D) := by
  unfold QueriesModel.queries initial
  apply bind_tail
  intro absorbed
  repeat' (conv_lhs => whnf
           conv_rhs => whnf
           apply bind_tail
           intro value)
  rfl
#print axioms source_eq
end AspisR1.JGg_QueryFactor
