import S2W_DigestExtraction
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_ExtractionGap
open Aeneas Aeneas.Std Result

/-- Two extensions of the SAME result-valued source function. The D188
observations see only the first projection, so neither carrier law follows
from those observations. These are interface models, not native executions. -/
def retain {I O : Type} (f : I → Result O) (input : I) (state : Bool) :=
  (f input,state)
def change {I O : Type} (f : I → Result O) (input : I) (state : Bool) :=
  (f input,!state)

theorem indistinguishable {I O : Type} (f : I → Result O) :
    (∀ input state, (retain f input state).1 = f input) ∧
    (∀ input state, (change f input state).1 = f input) ∧
    (∀ input state, (retain f input state).1 = (change f input state).1) :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem different {I O : Type} (f : I → Result O) (input : I) :
    (retain f input false).2 ≠ (change f input false).2 := by
  change false ≠ true
  decide

/-- Even a fixed, inhabited D188 instance does not constrain an added state
projection. No trust or hypothesis is added to a deployed theorem here. -/
theorem extraction_does_not_determine_carrier
    (ops : AdapterRw.Ops) (first : S2W_ExtractionBoundary.First)
    (second : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops first second hashv)
    (self : AdapterRw.SolanaDigest) (parts : S2Z.Oracle.Parts) :
    (retain (ops.op43 self) parts false).1 =
      S2W_DigestExtraction.digest hashv self parts ∧
    (change (ops.op43 self) parts false).1 =
      S2W_DigestExtraction.digest hashv self parts ∧
    (retain (ops.op43 self) parts false).2 ≠
      (change (ops.op43 self) parts false).2 :=
  ⟨extraction.digestSource self parts,extraction.digestSource self parts,different _ _⟩

#print axioms indistinguishable
#print axioms different
#print axioms extraction_does_not_determine_carrier
end AspisR1.BEf_ExtractionGap
end
