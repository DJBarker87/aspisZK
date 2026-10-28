import R1Z.PV_RDEA_AppendExecution
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_AppendNoGrowth
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath

/-- Already-reserved byte append has no allocator call, even in a world left
by arbitrary earlier witness computation. Only the tail memory is written. -/
def appended (b : Buffer U8) (tail : List U8)
    (fits : b.values.length+tail.length≤b.capacity) : Buffer U8 :=
  ⟨b.address,b.capacity,b.values++tail,by simpa only [List.length_append] using fits⟩

theorem complete {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F)
    (fits : b.values.length+tail.length≤b.capacity) :
    PV_RDEA_AppendExecution.append step shape b tail w =
      (.ok (appended b tail fits),
        {w with memory:=PV_RDB1_Append.writeTail b.address b.values.length tail w.memory}) := by
  have enough : tail.length≤b.capacity-b.values.length := by omega
  have hr : PV_RDB1_Append.reserve step 18446744073709551615 9223372036854775807 shape b tail.length w =
      ⟨.ok (),b,w⟩ := by
    simp only [PV_RDB1_Append.reserve,enough,ite_true]
  unfold PV_RDEA_AppendExecution.append
  dsimp only
  split <;> rename_i h
  · rw [hr] at h
    cases h
  · simp only [hr]
    rfl

theorem header {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F)
    (fits : b.values.length+tail.length≤b.capacity) :
    (PV_RDEA_AppendExecution.append step shape b tail w).1=.ok (appended b tail fits) ∧
    (PV_RDEA_AppendExecution.append step shape b tail w).2.allocator=w.allocator ∧
    (PV_RDEA_AppendExecution.append step shape b tail w).2.history=w.history := by
  rw [complete step shape b tail w fits]
  exact ⟨rfl,rfl,rfl⟩

#print axioms complete
#print axioms header
end R1Z.PV_RDEA_AppendNoGrowth
