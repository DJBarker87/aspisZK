import RPz7_SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_BatchInterface
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Full frozen batch_merkle signature, including arbitrary which, not just
its TX1 specialization0. Hash is the deployed Unit carrier; hashv interprets
its runtime digest calls. Native realization remains an OPEN producer. -/
structure Input where
 hashv : SdkC_Source.Parts → Result SdkC_Source.Digest
 proof : Slice U8
 prepared : verifier.Prepared
 folded : Array U8 32#usize
 which : Usize
structure Observation where
 afterInput : Input
 reply : Result (core.result.Result Unit verifier.Error)
 log : SdkC_Source.Log
 enteredValues : Bool
/-- Full Result, immutable input frame and exact attempted digest prefix.
The wrapper always enters values at SAME queries/roots/which/hash. -/
def RowSpec_081 (native : Input → Observation) : Prop :=
 ∀ i,
 (native i).afterInput = i ∧
 (native i).enteredValues = true ∧
 ∀ before,
 SdkC_Source.run i.hashv
  (SdkC_BatchSource.mapCode Op5T_Install.currentError
   (SdkC_BatchSource.code (SdkC_Source.dictionary i.hashv) () i.proof
    i.prepared.queries i.prepared.roots i.folded i.which)) before =
 ((native i).reply,before ++ (native i).log)
#print RowSpec_081
end AspisR1.NLJ_BatchInterface
end
