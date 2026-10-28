import R1Z.PV_RDEA_JoinValues
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_JoinConsumer
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath

def consume {S F R : Type} (e : Outcome (Buffer U8) S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (next : List U8 → World S F → R) : R :=
  match e.1 with
  | .error err => failure err e.2
  | .ok b => next b.values e.2

/-- Actual concrete clone/append operations are instantiated here. Failure is
handled with the post-request world; success transports the old contents law
while retaining the entire actual world rather than a fresh-output world. -/
theorem endpoint {S F R : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (next : List U8 → World S F → R) :
    let e := sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w
    consume e failure next =
      (match e.1 with
       | .error err => failure err e.2
       | .ok _ => next (PV_RDEA_PushValues.value base path absolute needSep) e.2) := by
  dsimp only
  unfold consume
  split <;> rename_i h
  · rfl
  · rw [PV_RDEA_JoinValues.success_value step shape address absolute needSep base path w _ h]

#print axioms endpoint
end R1Z.PV_RDEA_JoinConsumer
