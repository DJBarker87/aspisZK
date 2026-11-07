import NMS_LogMap
set_option autoImplicit false
namespace NMS_TryFold
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets
abbrev R (A : Type) := core.result.Result A PE

def step {E A B : Type} (m : NJU_Log.Run E (R A))
 (k : A → NJU_Log.Run E (R B)) : NJU_Log.Run E (R B) := do
 let reply ← m
 let flow ← core.result.Result.Insts.CoreOpsTry.branch reply
 match flow with
 | .Continue a => k a
 | .Break residual =>
  liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   B (core.convert.FromSame PE) residual

def simple {E A B : Type} (m : NJU_Log.Run E (R A))
 (k : A → NJU_Log.Run E (R B)) : NJU_Log.Run E (R B) :=
 NJU_Log.bind m fun reply => match reply with
 | .Ok a => k a
 | .Err error => pure (.Err error)

theorem normalize {E A B : Type} (m : NJU_Log.Run E (R A))
 (k : A → NJU_Log.Run E (R B)) : step m k = simple m k := by
 cases m with
 | mk result events =>
  cases result with
  | ok reply => cases reply <;> rfl
  | fail _ => rfl
  | div => rfl

theorem mapped {E F A B C D : Type} (event : E → F) (value : A → C) (output : B → D)
 (m : NJU_Log.Run E (R A)) (n : NJU_Log.Run F (R C))
 (k : A → NJU_Log.Run E (R B)) (l : C → NJU_Log.Run F (R D))
 (first : NMS_LogMap.run event (NMS_LogMap.rust value) m = n)
 (next : ∀ a, NMS_LogMap.run event (NMS_LogMap.rust output) (k a) = l (value a)) :
 NMS_LogMap.run event (NMS_LogMap.rust output) (step m k) = step n l := by
 rw [normalize,normalize]
 apply NMS_LogMap.bind event (NMS_LogMap.rust value) (NMS_LogMap.rust output) m n _ _ first
 intro reply
 cases reply with
 | Ok a => exact next a
 | Err error => rfl

theorem lifted {E F A B : Type} (event : E → F) (value : A → B) (r : Result A) :
 NMS_LogMap.run event value (liftM r : NJU_Log.Run E A) =
 (liftM (NMS_LogMap.result value r) : NJU_Log.Run F B) := rfl

theorem lift_bind {E F A B C : Type} (event : E → F) (output : B → C)
 (r : Result A) (k : A → NJU_Log.Run E B) (l : A → NJU_Log.Run F C)
 (next : ∀ a, NMS_LogMap.run event output (k a) = l a) :
 NMS_LogMap.run event output (NJU_Log.bind (liftM r) k) =
 NJU_Log.bind (liftM r) l := by
 apply NMS_LogMap.bind event id output _ _ k l _ next
 rw [lifted,NMS_LogMap.result_id]

#print axioms normalize
#print axioms mapped
#print axioms lifted
#print axioms lift_bind
end NMS_TryFold
