import BEk_Projection
import BEi_RecorderCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_Recorder
open Aeneas Aeneas.Std Result SdkC_Source

/-- Explicit entry observation: the input is recorded before the call returns.
A pending attempt is not an invented returned failure. -/
structure Attempt where
  parts : Parts
  returned : Option (Result Digest)

abbrev History := List Attempt

def enter (before : History) (parts : Parts) : History :=
  before ++ [⟨parts,none⟩]

def complete (before : History) (parts : Parts) (answer : Result Digest) : History :=
  before ++ [⟨parts,some answer⟩]

def completed (before : Log) : History :=
  before.map (fun call => ⟨call.parts,some call.returned⟩)

/-- The pending prefix contains the attempted address even before a return. -/
theorem entered (before : History) (parts : Parts) :
    (enter before parts).map Attempt.parts = before.map Attempt.parts ++ [parts] := by
  simp only [enter,List.map_append,List.map_cons,List.map_nil]

/-- Returning replaces the last pending entry, retaining every prior occurrence. -/
theorem finish (before : History) (parts : Parts) (answer : Result Digest) :
    complete before parts answer =
      (enter before parts).take before.length ++ [⟨parts,some answer⟩] := by
  simp only [complete,enter,List.take_left]

/-- The Rust infallible-return recorder is the successful subcase of this law. -/
theorem completed_append (before : Log) (parts : Parts) (answer : Result Digest) :
    completed (before ++ [⟨parts,answer⟩]) = complete (completed before) parts answer := by
  simp only [completed,complete,List.map_append,List.map_cons,List.map_nil]

#print axioms entered
#print axioms finish
#print axioms completed_append
end AspisR1.BEl_Recorder
end
