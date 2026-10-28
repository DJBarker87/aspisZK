import R1Z.PV_RDEA_CloneExecution
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_AppendExecution
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint
open PV_RDB1_Append PV_RDEA_AppendRequests

/-- Concrete byte append preserving the world on errors and the actual tail
copy on success. It is usable by the error-aware clone-first consumer. -/
def append {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F) :
    Outcome (Buffer U8) S F :=
  let e := reserve step 18446744073709551615 9223372036854775807 shape b tail.length w
  match h : e.returned with
  | .error err => (.error err,e.world)
  | .ok () =>
    let b' : Buffer U8 := ⟨e.buffer.address,e.buffer.capacity,e.buffer.values++tail,by
      rw [List.length_append,reserve_values]
      exact reserve_capacity step _ _ shape b tail.length w h⟩
    (.ok b',{e.world with memory := writeTail e.buffer.address e.buffer.values.length tail e.world.memory})

theorem append_sizes {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (b : Buffer U8)
    (tail : List U8) (w : World S F) :
    sizes (append step shape b tail w).2.history =
      sizes w.history ++ requests 18446744073709551615 9223372036854775807
        b.values.length b.capacity tail.length := by
  unfold append
  dsimp only
  split <;> exact reserve_requests step _ _ shape width b tail.length w

#print axioms append_sizes
end R1Z.PV_RDEA_AppendExecution
