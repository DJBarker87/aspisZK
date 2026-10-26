import BEi_BatchPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEj_ReifiedBatch
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- Concrete source-carrier interface. These are the actual source arrays,
not parsed-model replacements. Physical borrow geometry/admission is not
invented here: associating a reached native cut with this interface is OPEN. -/
structure Input where
  proof : Slice U8
  prepared : AspisR1Stage2.verifier.Prepared
  folded : Array U8 32#usize

def ordinal (slot : Fin 2) : Usize := if slot.val = 0 then 0#usize else 1#usize

def nativeCode (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2) :=
  Port9OR_Batch.code Port4B_Install.leaves (SdkC_Source.dictionary hashv) ()
    input.proof input.prepared input.folded (ordinal slot)

def sourceCode (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2) :=
  SdkC_BatchSource.code (SdkC_Source.dictionary hashv) () input.proof
    input.prepared.queries input.prepared.roots input.folded (ordinal slot)

/-- Intensional equality of the two existing source effect bodies. This is
stronger than equality of erased Results, but is NOT a physical runtime law. -/
theorem programs (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2) :
    nativeCode hashv input slot = sourceCode hashv input slot := rfl

/-- Exact local BEh law derived from explicit operational steps on that body.
The unproved native physical-to-operational association is visible as steps;
this theorem is NOT the requested unconditional observation instance. -/
theorem of_steps {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2)
    (state after : S) (before log : Log)
    (value : Result (core.result.Result Unit AspisR1Stage2.verifier.Error))
    (steps : Executes call (nativeCode hashv input slot) state before value after log) :
    BEh_Scope.Law (value,after,log)
      (BEf_Carrier.run call (sourceCode hashv input slot) state before) := by
  rw [programs] at steps
  exact BEi_CutProjection.observation call _ state after before log value steps

/-- A two-slot instance is established for the REIFIED source denotations.
No physical native function is silently identified with either interpreter. -/
theorem reified_observation {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) :
    BEh_Scope.BothSlots (fun (_ : Input) (_ : Fin 2) (_ : S) => True)
      (fun input slot state before => BEf_Carrier.run call (nativeCode hashv input slot) state before)
      (fun input slot state before => BEf_Carrier.run call (sourceCode hashv input slot) state before) := by
  intro input slot state before _
  rw [programs]
  exact BEh_Scope.reflexive _

#print axioms programs
#print axioms of_steps
#print axioms reified_observation
end AspisR1.BEj_ReifiedBatch
end
