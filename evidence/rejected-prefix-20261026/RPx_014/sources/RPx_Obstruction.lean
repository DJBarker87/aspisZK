import RPx_Duplicates
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Obstruction
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Runtime F3T_ByteCarrier

/-- Exact current runtime binding permits arbitrary fresh external prefixes.
This is an interface counterexample, not a counterexample to shipped code. -/
theorem arbitrary {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : F3T_TwoPass.Verifier)
    (P : ByteProver) (runtime : Runtime) (law : StoredCarrierBinding c D rust P runtime)
    (n : Nat) :
    ∃ extended : Runtime, StoredCarrierBinding c D rust P extended ∧
      ∀ H : Bytes → State,
        (eval H extended).2=(eval H runtime).2 ∧
        (eval H extended).1.length=n+(eval H runtime).1.length ∧
        n≤FS.firstReads FS.emptyTable (eval H extended).1 := by
  refine ⟨RPx_RuntimePrefix.prepend (RPx_Fresh.prelude n) runtime,
    RPx_RuntimePrefix.binding c D rust P runtime law _,?_⟩
  intro H
  rw [RPx_RuntimePrefix.evaluation]
  refine ⟨rfl,?_,?_⟩
  · rw [List.length_append,RPx_Fresh.occurrence_count]
  · rw [←RPx_Fresh.first_read_count n H]
    exact RPx_Duplicates.append_mono _ _

/-- No finite rejected-prefix Q follows from binding. Existing accepted
observations, if present, are preserved by the same construction. -/
theorem exceeds {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : F3T_TwoPass.Verifier)
    (P : ByteProver) (runtime : Runtime) (law : StoredCarrierBinding c D rust P runtime)
    (Q : Nat) :
    ∃ extended : Runtime, StoredCarrierBinding c D rust P extended ∧
      ∀ H : Bytes → State,
        (eval H extended).2=(eval H runtime).2 ∧
        Q+2965<FS.firstReads FS.emptyTable (eval H extended).1 := by
  obtain ⟨extended,binding,count⟩ := arbitrary c D rust P runtime law (Q+2966)
  refine ⟨extended,binding,?_⟩
  intro H
  obtain ⟨same,_,lower⟩ := count H
  exact ⟨same,by omega⟩

#print axioms arbitrary
#print axioms exceeds
end AspisR1.RPx_Obstruction
end
