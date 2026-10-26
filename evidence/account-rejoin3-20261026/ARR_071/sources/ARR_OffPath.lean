import ARR_WorldCompatibility
import OracleProgramReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_OffPath
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- There is always a different 32-byte oracle answer. -/
theorem different (s : State) : ∃ d : State, d ≠ s := by
  by_cases zero : s 0 = 0
  · refine ⟨fun _ => 1,?_⟩
    intro same
    have atZero := congrFun same 0
    have impossible : (1 : AspisV8R19.DuplexFrames.Byte) = 0 := atZero.trans zero
    exact (by decide : (1 : AspisV8R19.DuplexFrames.Byte) ≠ 0) impossible
  · refine ⟨fun _ => 0,?_⟩
    intro same
    exact zero (congrFun same.symm 0)

/-- A world can be changed off the entire original execution's query path
without changing any adaptive choice, rejection, acceptance, cost or outcome. -/
theorem change {X : Type} (p : Program Bytes State X) (H : Bytes → State)
    (address : Bytes) (fresh : address ∉ (eval H p).1.map Prod.fst) (answer : State) :
    eval (fun x => if x = address then answer else H x) p = eval H p := by
  apply OracleProgramReplay.eval_eq_of_agrees
  intro x queried
  have other : x ≠ address := by
    rintro rfl
    exact fresh queried
  exact if_neg other

/-- Exact counter-world for the global P1/RuntimeSyscall factory: a fixed
native return at an UNUSED address rules out its witness in an outcome-identical
world. This applies to arbitrary programs, including the full account program. -/
theorem incompatible_same_run {X : Type} (p : Program Bytes State X) (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest)
    (returned : hashv parts = .ok digest)
    (fresh : flatten parts ∉ (eval H p).1.map Prod.fst) :
    ∃ K : Bytes → State, eval K p = eval H p ∧
      ¬ ARR_WorldCompatibility.Compatible K hashv := by
  obtain ⟨d,different⟩ := different (decodeState digest)
  let K : Bytes → State := fun x => if x = flatten parts then d else H x
  refine ⟨K,change p H _ fresh d,?_⟩
  intro compatible
  have same := compatible parts digest returned
  have atAddress : K (flatten parts) = d := if_pos rfl
  exact different ((same.trans atAddress).symm)

/-- An acceptance-guarded global native-oracle factory requires EVERY address
where the fixed native hash ever returns to have been queried by EVERY accepted
run. Thus guarding on acceptance does not repair off-path overconstraint. -/
theorem factory_forces_reads {X : Type} (p : Program Bytes State X)
    (accepts : X → Prop) (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : accepts (eval H p).2)
    (factory : ∀ K : Bytes → State, accepts (eval K p).2 →
      ∃ sha256 : Bytes → State, S2W_ExtractionBoundary.P1 sha256 K ∧
        S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest)
    (returned : hashv parts = .ok digest) :
    flatten parts ∈ (eval H p).1.map Prod.fst := by
  by_contra fresh
  obtain ⟨K,same,incompatible⟩ := incompatible_same_run p H hashv parts digest returned fresh
  have acceptedK : accepts (eval K p).2 := by rw [same]; exact accepted
  exact incompatible ((ARR_WorldCompatibility.iff_witness K hashv).mpr (factory K acceptedK))

#print axioms different
#print axioms change
#print axioms incompatible_same_run
#print axioms factory_forces_reads
end AspisR1.ARR_OffPath
end
