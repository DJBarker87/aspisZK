import PV_L1E_OriginalCountSkeleton
set_option autoImplicit false
namespace PV_SKW_L1
open PV_RJ4IDB PV_L1E_CountSkeleton PV_L1E_OriginalCountSkeleton
open R1Z.SideChannelL1AttemptRecord
abbrev I := Nat × Nat
/-- Explicit two-attempt model: rejection at zero, success thereafter; state advances. -/
def owner : Owner Nat Nat := fun k s =>
 (⟨[.call .callback k,.checkerReturn (k != 0)],
   if k = 0 then .retry else .done (s+1)⟩,s+1)
def runAt (i : I) : Run Nat × Nat := run owner i.1 i.2 0
/-- Preserve each retry and the successful public return count from the run itself. -/
def encode (r : Run Nat × Nat) : NativeTrace Nat :=
 let rejected := r.1.attempts.zipIdx |>.filterMap fun (a,k) =>
   match a.result with | .retry => some (NativeEvent.rejection k) | _ => none
 match r.1.result with
 | .done p => ⟨rejected ++ [.count p.attempts],.success p.proof⟩
 | .stop _ => ⟨rejected,.failure [69]⟩
 | .retry => ⟨rejected,.diverge⟩
def adapt (_ : I) (r : Run Nat × Nat) : Trace Nat := modelTrace (encode r)
structure Instance where
 actual : I → List Nat × List Nat
 native : I → NativeTrace Nat
 sourceWorld : I → Trace Nat
 bodyWorld : I → Trace Nat
 originalWorld : I → Trace Nat
def instance : Instance :=
 ⟨fun i => let t := adapt i (runAt i); (counts t.events,rejections t.events),
  fun i => encode (runAt i),fun i => adapt i (runAt i),
  fun i => adapt i (runAt i),fun i => adapt i (runAt i)⟩
/-- The four D466 original-owner links hold together on the same recursive run. -/
theorem satisfiable : ∃ x : Instance,
 PV_L1E_Link_CountAcquisition x.actual x.sourceWorld ∧
 PV_L1E_Link_BodyWrapper x.sourceWorld x.bodyWorld ∧
 PV_L1E_Link_OriginalRetry x.bodyWorld (fun _ => owner) (fun _ => 0)
   Prod.fst Prod.snd adapt ∧
 PV_L1E_Link_NativeD163 x.native (fun _ => owner) (fun _ => 0)
   Prod.fst Prod.snd adapt := by
 exact ⟨instance,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl)⟩
/-- Also check the four links of the generic COUNT skeleton, without replacing them. -/
theorem generic_satisfiable : ∃ x : Instance,
 PV_L1E_Link_CountAcquisition x.actual x.sourceWorld ∧
 PV_L1E_Link_BodyWrapper x.sourceWorld x.bodyWorld ∧
 PV_L1E_Link_RetryJoin x.bodyWorld x.originalWorld ∧
 PV_L1E_Link_NativeOriginal x.originalWorld x.native := by
 exact ⟨instance,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl)⟩
theorem nondegenerate : instance.actual (2,0) = ([2],[0]) ∧
 (runAt (2,0)).2 = 2 ∧ (instance.native (2,0)).terminal = .success 2 := by
 exact ⟨rfl,rfl,rfl⟩
#print axioms satisfiable
#print axioms generic_satisfiable
#print axioms nondegenerate
end PV_SKW_L1
