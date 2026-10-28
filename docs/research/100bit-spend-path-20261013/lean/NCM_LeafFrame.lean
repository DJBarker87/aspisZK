import NCM_LeafSelected

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_LeafFrame
open Aeneas Aeneas.Std Result ControlFlow MultiproofConeRef NCE_OpeningCuts
open NCE_LeafCuts Port4B_LeafStep

/-- Leaf insertion never changes the binary-node cursor. This includes the
successful duplicate branch, independently of digest consistency. -/
theorem next_cursor (s : reference.Scratch) (index : U32) (digest : CheckpointBytes5Effect.Digest)
    (room : s.n.val < 16) (after : reference.Scratch)
    (returned : MultiproofConeLeafContent.next s index digest room = some after) :
    after.«at» = s.«at» := by
  unfold MultiproofConeLeafContent.next at returned
  split at returned
  · split at returned <;> cases returned
    rfl
  · cases returned
    rfl

/-- The source ControlFlow tuple is joined to the whole SAME caller, with
its binary cursor retained. This is not an independently selected scratch. -/
theorem continued (s : Carrier) (after : reference.Scratch) (pos : Usize)
    (cursor : after.«at» = s.scratch.«at») :
    returnedCarrier s (project s.scratch pos (some after)) = {s with scratch:=after} := by
  cases s with
  | mk prepared proof scratch log =>
    cases scratch with
    | mk idx val n nodeCursor =>
      cases after with
      | mk nextIdx nextVal nextN nextAt =>
        cases cursor
        rfl

/-- Duplicate failure retains the exact current scratch and issued prefix. -/
theorem rejected (s : Carrier) (pos : Usize) :
    returnedCarrier s (project s.scratch pos none) = s := by
  rfl

#print axioms next_cursor
#print axioms continued
#print axioms rejected
end AspisR1.NCM_LeafFrame
end
