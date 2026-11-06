import NKI_LevelsCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsNative
open Aeneas Aeneas.Std Result
open NJX_DigestCohort (O)
open NJX_AppendDomains (Frontier High)
open NJX_AppendFold (State)
inductive Trace (index : U64) (f : Frontier) (o : O) (s : High) (child : Fin 20 → State) : List (Fin 20) → State → State → Prop
 | nil (before) : Trace index f o s child [] before before
 | cons {i is before middle after} :
  NKI_LevelsFrame.call index f o s i=ok (child i) →
  NKI_LevelsCut.Cut index i (NJX_AppendDomains.frontier f i) o (NJX_AppendDomains.high s i)
   before (child i) middle middle index i.val (i.val+1) (NJX_AppendDomains.frontier f i) o (NJX_AppendDomains.high s i) 1 4 →
  Trace index f o s child is middle after → Trace index f o s child (i::is) before after
/-- Native one-step packets chained along the source20level control, with
all complete4cell states. Generic support parameters are internally supplied
by234 in235, not a child-success assumption at either root. -/
theorem source (index : U64) (f : Frontier) (o : O) (s : High) (child : Fin 20 → State)
 (calls : ∀ i,NKI_LevelsFrame.call index f o s i=ok (child i))
 {is : List (Fin 20)} {before after : State} (tr : NJX_AppendFold.Trace child is before after) :
 Trace index f o s child is before after := by
 induction tr with
 | nil before=>exact .nil before
 | @cons i is before middle after cm cut tr ih=>
  exact .cons (calls i) (NKI_LevelsCut.source index i _ o _ before (child i) middle cut) ih
#print axioms source
end AspisR1.NKI_LevelsNative
end
