import R1TraceSpendWitness
import R1SpendBaseDescent
import R1SpendDataMap
import R1ExactBaseProjection

/-! A computable M31 witness selector from a wide trace. The branch test is
performed after explicit base projection; the theorem below shows this agrees
with the existing noncomputable wide-field path selector when the trace is
base-typed. This constructs data only and proves no spend validity. -/
set_option autoImplicit false

namespace AspisR1.ComputableTraceWitness

open R0P
open AspisV8R15.ExactTowerBase
open AspisWideTower
open AspisR1.SpendRelation

abbrev E := WideExact
abbrev F := AspisR1.ExactBaseProjection.embed.fieldRange

def pathFromTrace (A : Trace E) : Fin 24 → Bool × Digest M31Exact :=
  fun level =>
    let b := pathBaseRow level
    let left : Digest M31Exact := fun i =>
      AspisR1.ExactBaseProjection.project
        (A ⟨i.val, by omega⟩ (succRow b))
    let right : Digest M31Exact := fun i =>
      AspisR1.ExactBaseProjection.project
        (A ⟨8 + i.val, by omega⟩ (succRow b))
    if AspisR1.ExactBaseProjection.project (A 0 b) = 0 then
      (false, right)
    else
      (true, left)

def fromTrace (A : Trace E) (v0 v1 v2 : Fin (2^30)) : Wspend :=
  { inputValue := v0
    outputValue := v1
    changeValue := v2
    sk := SpendDataMap.digest AspisR1.ExactBaseProjection.project (traceSk A)
    salt := SpendDataMap.digest AspisR1.ExactBaseProjection.project (traceSalt A)
    path := pathFromTrace A
    pair := SpendDataMap.pair AspisR1.ExactBaseProjection.project (AspisR1.InputPair.leaf A)
    recipientOwner := SpendDataMap.digest AspisR1.ExactBaseProjection.project
      (AspisR1.OutputNotes.chunk A 27)
    recipientSalt := SpendDataMap.digest AspisR1.ExactBaseProjection.project
      (AspisR1.OutputNotes.salt A 28 29)
    changeOwner := SpendDataMap.digest AspisR1.ExactBaseProjection.project
      (AspisR1.OutputNotes.chunk A 30)
    changeSalt := SpendDataMap.digest AspisR1.ExactBaseProjection.project
      (AspisR1.OutputNotes.salt A 31 32) }

theorem pathFromTrace_eq (A : Trace E) (hA : BaseTyped F A) :
    pathFromTrace A =
      SpendDataMap.path AspisR1.ExactBaseProjection.project (tracePath A) := by
  funext level
  let b := pathBaseRow level
  have hzero : AspisR1.ExactBaseProjection.project (A 0 b) = 0 ↔ A 0 b = 0 := by
    constructor
    · intro hp
      have hc : A 0 b ∈ F := hA 0 (by decide) b
      have he := AspisR1.ExactBaseProjection.embed_project_of_mem_fieldRange hc
      rw [hp] at he
      simpa using he.symm
    · intro hz
      rw [hz]
      rfl
  classical
  by_cases hz : A 0 b = 0
  · have hp : AspisR1.ExactBaseProjection.project (A 0 b) = 0 := hzero.mpr hz
    simp [pathFromTrace, tracePath, SpendDataMap.path, SpendDataMap.digest,
      AspisR1.ExactBaseProjection.project, b, hz, hp]
  · have hp : AspisR1.ExactBaseProjection.project (A 0 b) ≠ 0 :=
      fun h => hz (hzero.mp h)
    simp [pathFromTrace, tracePath, SpendDataMap.path, SpendDataMap.digest,
      AspisR1.ExactBaseProjection.project, b, hz, hp]

theorem fromTrace_eq_projected_existing (A : Trace E) (v0 v1 v2 : Fin (2^30))
    (hA : BaseTyped F A) :
    fromTrace A v0 v1 v2 =
      AspisR1.SpendBaseDescent.projectWitness
        (AspisR1.TraceSpendWitness.fromTrace A v0 v1 v2) := by
  rw [fromTrace, AspisR1.SpendBaseDescent.projectWitness,
    SpendDataMap.witness, pathFromTrace_eq A hA]
  rfl

#print axioms pathFromTrace_eq
#print axioms fromTrace_eq_projected_existing

end AspisR1.ComputableTraceWitness
