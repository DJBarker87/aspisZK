import R1Z.PV_RDEA_PathSchedule
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_StatefulPath
open PV_RDB1_V183_ReserveWorld PV_RDB1_Append

/-- Unlike Result (value × world), failure here retains the allocator world. -/
abbrev Outcome (A S F : Type) := Except PV_RDB1_V183_ReserveWorld.Error A × World S F

def bind {A B S F : Type} (a : Outcome A S F)
    (next : A → World S F → Outcome B S F) : Outcome B S F :=
  match a.1 with
  | .error e => (.error e,a.2)
  | .ok v => next v a.2

theorem bind_error {A B S F : Type} (err : PV_RDB1_V183_ReserveWorld.Error) (w : World S F)
    (next : A → World S F → Outcome B S F) :
    bind (.error err,w) next=(.error err,w) := rfl

def clear {S F : Type} (b : Buffer U8) (w : World S F) : Outcome (Buffer U8) S F :=
  (.ok (PV_RDB1_V178.cleared b),PV_RDB1_V178.dropBytes b.values.length w)

def clearReference {S F : Type} (b : Buffer U8) (w : World S F) : Outcome (Buffer U8) S F :=
  (.ok (PV_RDB1_V178.cleared b),w)

theorem clear_complete {S F : Type} (b : Buffer U8) (w : World S F) :
    clear b w=clearReference b w := by
  simp only [clear,clearReference,PV_RDB1_V178.byte_drops]

def sourcePush {S F : Type}
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (b : Buffer U8) (path : List U8) (w : World S F) :
    Outcome (Buffer U8) S F :=
  bind (if absolute then clear b w else (.ok b,w)) fun b w =>
    bind (if !absolute && needSep then append b [47#u8] w else (.ok b,w)) fun b w =>
      append b path w

def repairedPush {S F : Type}
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (b : Buffer U8) (path : List U8) (w : World S F) :
    Outcome (Buffer U8) S F :=
  bind (if absolute then clearReference b w else (.ok b,w)) fun b w =>
    bind (if !absolute && needSep then append b [47#u8] w else (.ok b,w)) fun b w =>
      append b path w

theorem push_complete {S F : Type}
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (b : Buffer U8) (path : List U8) (w : World S F) :
    sourcePush append absolute needSep b path w=repairedPush append absolute needSep b path w := by
  simp only [sourcePush,repairedPush,clear_complete]

def sourceJoin {S F : Type}
    (clone : List U8 → World S F → Outcome (Buffer U8) S F)
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (base path : List U8) (w : World S F) :
    Outcome (Buffer U8) S F :=
  bind (clone base w) fun b w => sourcePush append absolute needSep b path w

theorem join_complete {S F : Type}
    (clone : List U8 → World S F → Outcome (Buffer U8) S F)
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (base path : List U8) (w : World S F) :
    sourceJoin clone append absolute needSep base path w =
      bind (clone base w) (fun b w => repairedPush append absolute needSep b path w) := by
  simp only [sourceJoin,push_complete]

theorem clone_failure_world {S F : Type}
    (clone : List U8 → World S F → Outcome (Buffer U8) S F)
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (base path : List U8) (w after : World S F) (err : PV_RDB1_V183_ReserveWorld.Error)
    (h : clone base w=(.error err,after)) :
    sourceJoin clone append absolute needSep base path w=(.error err,after) := by
  simp only [sourceJoin,h,bind_error]

/-- Concrete consumed law retains failure world as well as the success world;
allocation failure is passed to the error-aware consumer, never to ok empty. -/
theorem endpoint {S F R : Type}
    (clone : List U8 → World S F → Outcome (Buffer U8) S F)
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (absolute needSep : Bool) (base path : List U8) (w : World S F)
    (consume : Outcome (Buffer U8) S F → R) :
    consume (sourceJoin clone append absolute needSep base path w) =
      consume (bind (clone base w) fun b w => repairedPush append absolute needSep b path w) := by
  rw [join_complete]

#print axioms bind_error
#print axioms clear_complete
#print axioms push_complete
#print axioms join_complete
#print axioms clone_failure_world
#print axioms endpoint
end R1Z.PV_RDEA_StatefulPath
