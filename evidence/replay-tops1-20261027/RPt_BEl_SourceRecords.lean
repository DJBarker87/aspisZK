import RPt_BEl_CoordinateLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_SourceRecords
open Aeneas Aeneas.Std Result SdkC_Source

def parts (input : Parts) : List (List U8) := input.val.map Subtype.val

def query (q : Query) : BEl_FullLog.Record U8 (Result Digest) :=
  ⟨parts q.parts,q.returned⟩

def log (history : Log) := history.map query

theorem map_injective {A B : Type} (f : A → B) (injective : Function.Injective f)
    (left right : List A) (same : left.map f = right.map f) : left = right := by
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons b bs => cases same
  | cons a tail ih => cases right with
    | nil => cases same
    | cons b bs =>
      have h := List.cons.inj same
      rw [injective h.1,ih bs h.2]

theorem parts_injective (left right : Parts) (same : parts left = parts right) :
    left = right := by
  apply Subtype.ext
  exact map_injective (fun p : Slice U8 => p.val) Subtype.val_injective left.val right.val same

theorem query_injective (left right : Query) (same : query left = query right) :
    left = right := by
  have inputs := parts_injective left.parts right.parts (congrArg BEl_FullLog.Record.input same)
  have returned := congrArg BEl_FullLog.Record.returned same
  cases left
  cases right
  exact congrArg₂ Query.mk inputs returned

theorem log_injective (left right : Log) (same : log left = log right) : left = right :=
  map_injective query (fun _ _ h => query_injective _ _ h) left right same

/-- Kani's universal part-length/byte/reply projections suffice for the exact
SdkC log carrier, including slice proof fields by proof irrelevance. This says
nothing about equality of machine pointer addresses or allocation geometry. -/
theorem of_coordinates (left right : Log)
    (sizes : ∀ i, BEl_CoordinateLog.lengths (log left) i = BEl_CoordinateLog.lengths (log right) i)
    (bytes : ∀ i p j, BEl_CoordinateLog.byte (log left) i p j = BEl_CoordinateLog.byte (log right) i p j)
    (returned : ∀ i, BEl_CoordinateLog.reply (log left) i = BEl_CoordinateLog.reply (log right) i) :
    left = right :=
  log_injective left right (BEl_CoordinateLog.ext _ _ sizes bytes returned)

#print axioms map_injective
#print axioms parts_injective
#print axioms query_injective
#print axioms log_injective
#print axioms of_coordinates
end AspisR1.BEl_SourceRecords
end
