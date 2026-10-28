import R1Z.PV_RDB1_ResumeAudit
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_ResumeReplay
namespace V164
open R1Z.PV_RDB1_V164
theorem checked {M Q : Type} (lift : M → Result Q) (scale : Q → M → Result Q)
    (add mul : Q → Q → Result Q) (tag : M) (values : Slice M) (lambda : Q) :
    shipped lift scale add mul tag values lambda =
      reference lift scale add mul tag values lambda := by apply @R1Z.PV_RDB1_V164.complete
#print axioms checked
end V164

namespace V170
open R1Z.PV_RDB1_V170
open PV_RDB1_Pointer
theorem checked {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : PV_RDB1_V170_World.Buffer) (w : PV_RDB1_V170_World.World S F) :
    (ok (PV_RDB1_V170_World.native free b w) :
      Result (Unit × PV_RDB1_V170_World.World S F)) =
      ok (PV_RDB1_V170_World.reference free b w) := by apply @R1Z.PV_RDB1_V170.complete
#print axioms checked
end V170

namespace V182
open R1Z.PV_RDB1_V182
open PV_RDB1_V183_ReserveWorld
theorem checked {S F R : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8) (tail : List U8)
    (w : World S F) (handler : PV_RDB1_Append.Appended S F → Result R) :
    handler (PV_RDB1_Append.source step wordMax byteMax shape b tail w) =
      handler (PV_RDB1_Append.reference step wordMax byteMax shape b tail w) := by apply @R1Z.PV_RDB1_V182.world_complete
#print axioms checked
end V182

namespace V183
open R1Z.PV_RDB1_V183
open PV_RDB1_V183_ReserveWorld
theorem checked {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) :
    native step wordMax byteMax shape b additional w =
      reference step wordMax byteMax shape b additional w := by apply @R1Z.PV_RDB1_V183.complete
#print axioms checked
end V183

namespace V184
open R1Z.PV_RDB1_V184Bridge
open PV_RDB1_Pointer
theorem checked {T P F : Type} (p : NonNull T P)
    (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : PV_RDB1_V184_MoveMemory.Memory) (frame : F) (width : Nat) :
    ∃ o, deployed p b w memory frame = ok (historicalCast p,o) ∧
      PV_RDB1_V184_MoveWorld.referenceWorld b w memory frame width = ok o ∧
      o.returned = b.value.val.getLast? ∧ o.remaining.val = b.value.val.dropLast ∧
      o.buffer = b.address ∧ o.capacity = b.capacity ∧ o.world = w ∧
      o.memory = memory ∧ o.frame = frame := by apply @R1Z.PV_RDB1_V184Bridge.complete
#print axioms checked
end V184

namespace V186
open R1Z.PV_RDB1_V186
theorem checked {α : Type} (newCall : Result α) :
    defaultCall newCall = referenceCall newCall := by apply @R1Z.PV_RDB1_V186.complete
#print axioms checked
end V186

namespace V187
open R1Z.PV_RDB1_V187
theorem checked {T W : Type} (N : Usize) (v : alloc.vec.Vec T) (w : W)
    (finish : W → Result W) : reference N v w finish = deployed N v w finish := by apply @R1Z.PV_RDB1_V187.complete
#print axioms checked
end V187

namespace V195
open R1Z.PV_RDB1_V195
theorem checked {W : Type} (limbs : Array U32 8#usize) (world : W) :
    (ok (nativeBytes limbs,world) : Result (List U8 × W)) =
      ok ((chunks limbs).flatten,world) := by apply @R1Z.PV_RDB1_V195.complete
#print axioms checked
end V195

namespace V198
open R1Z.PV_RDB1_V198Bridge
open PV_RDB1_Copy PV_RDB1_V198
theorem checked (a b c d : U32) (out : List U8) :
    native a b c d out = write a b c d out := by apply @R1Z.PV_RDB1_V198Bridge.source_complete
#print axioms checked
end V198

namespace V219
open R1Z.PV_RDB1_V219
theorem checked {X A Q : Type} (initial : Four X → Result (Four A))
    (add : A → X → Result A) (finish : Four A → Result Q)
    (p : Array (Four X) 28#usize) :
    source initial add finish p = reference initial add finish p := by apply @R1Z.PV_RDB1_V219.complete
#print axioms checked
end V219

end R1Z.PV_RDB1_ResumeReplay
