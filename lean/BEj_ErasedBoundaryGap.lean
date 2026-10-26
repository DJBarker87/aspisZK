import BEj_BatchValue
import BEi_PhysicalGap
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEj_ErasedBoundaryGap
open Aeneas Aeneas.Std Result SdkC_Source BEj_ReifiedBatch

/-- On the EXACT installed batch inputs, erasure and the final carrier can
hold while the proposed recorder law fails. This is a countermodel to an
interface implication, not a counterexample to shipped native execution. -/
theorem installed {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (input : Input) (slot : Fin 2) (state : S) (before : Log) (extra : Query) :
    ∃ other : BEh_Scope.Outcome S Unit AspisR1Stage2.verifier.Error,
      other.1 = Op5T_Install.body Port4B_Install.leaves (SdkC_Source.dictionary hashv)
        input.proof input.prepared.queries input.prepared.roots input.folded (ordinal slot) () ∧
      other.2.1 = (BEf_Carrier.run call (sourceCode hashv input slot) state before).2.1 ∧
      ¬ BEh_Scope.Law other (BEf_Carrier.run call (sourceCode hashv input slot) state before) := by
  let out := BEf_Carrier.run call (sourceCode hashv input slot) state before
  have gap := BEi_PhysicalGap.extension out extra
  refine ⟨(out.1,out.2.1,out.2.2 ++ [extra]),?_,rfl,gap.2.2.2⟩
  have projected := BEf_Carrier.source call hashv binding (sourceCode hashv input slot) state before
  have value := congrArg Prod.fst projected
  change out.1 = _ at value
  exact value.trans (by
    rw [← programs]
    exact BEj_BatchValue.installed hashv input slot before)

/-- Even all retained facts independent of the newly introduced recorder
remain true in that decoration. It does not assume inconsistent admissions. -/
theorem retained {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2)
    (state : S) (before : Log) (extra : Query) (Facts : Prop) (facts : Facts) :
    Facts ∧ ∃ other : BEh_Scope.Outcome S Unit AspisR1Stage2.verifier.Error,
      other.1 = (BEf_Carrier.run call (sourceCode hashv input slot) state before).1 ∧
      other.2.1 = (BEf_Carrier.run call (sourceCode hashv input slot) state before).2.1 ∧
      ¬ BEh_Scope.Law other (BEf_Carrier.run call (sourceCode hashv input slot) state before) :=
  BEi_PhysicalGap.retained_facts _ extra Facts facts

#print axioms installed
#print axioms retained
end AspisR1.BEj_ErasedBoundaryGap
end
