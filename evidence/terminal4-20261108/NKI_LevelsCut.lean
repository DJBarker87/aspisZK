import NKI_LevelsFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsCut
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NJX_DigestCohort (O D)
open NJX_AppendFold (State)
/-- NJL_append_levels_step_cut (NJL_K059/060), full local-record arbitrary
prestate. Exact forwarded child arguments, four additions in order, full
poststate and level+1. Structural arrays are read-only. -/
def Cut (index : U64) (level : Fin 20) (frontier : D) (o : O) (high : NQ)
 (before child reply after : State) (passedIndex : U64) (passedLevel next : Nat)
 (passedFrontier : D) (passedOpened : O) (passedHigh : NQ) (calls adds : Nat) : Prop :=
 passedIndex=index ∧ passedLevel=level.val ∧ passedFrontier=frontier ∧ passedOpened=o ∧ passedHigh=high ∧
 calls=1 ∧ adds=4 ∧ next=level.val+1 ∧ after=reply ∧
 ∀ j,FIq_Native.field.QM31.add (before j) (child j)=ok (reply j)
theorem source (index : U64) (level : Fin 20) (frontier : D) (o : O) (high : NQ)
 (before child reply : State) (arithmetic : NJX_AppendFold.Cut before child reply reply 4) :
 Cut index level frontier o high before child reply reply index level.val (level.val+1) frontier o high 1 4 :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,arithmetic.2.2⟩
#print axioms source
end AspisR1.NKI_LevelsCut
end
