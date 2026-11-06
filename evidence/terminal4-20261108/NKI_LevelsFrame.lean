import NKI_AppendPacket
import NJX_AppendFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsFrame
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NJX_DigestCohort (O)
open NJX_AppendDomains (Frontier High)
open NJX_AppendFold (State)
def call (index : U64) (f : Frontier) (o : O) (s : High) (i : Fin 20) : Result State :=
 NKI_AppendPacket.cohort index (NJX_AppendDomains.level i) (NJX_AppendDomains.frontier f i) o (NJX_AppendDomains.high s i)
def run (index : U64) (f : Frontier) (o : O) (s : High) : List (Fin 20) → State → Result State
 | [],before=>ok before
 | i::is,before=>do
  let child←call index f o s i
  let middle←NJX_AppendFold.step before child
  run index f o s is middle
/-- Same-call child clauses are support parameters here, and are discharged
at all20arguments inside the235 root. Exact complete4cell frame chain. -/
theorem association (index : U64) (f : Frontier) (o : O) (s : High) (child : Fin 20 → State)
 (calls : ∀ i,call index f o s i=ok (child i)) (is : List (Fin 20)) (before : State) :
 run index f o s is before=NJX_AppendFold.run child is before := by
 induction is generalizing before with
 | nil=>rfl
 | cons i is ih=>
  simp only [run,NJX_AppendFold.run,calls,bind_tc_ok]
  apply congrArg
  funext middle
  exact ih middle
#print axioms association
end AspisR1.NKI_LevelsFrame
end
