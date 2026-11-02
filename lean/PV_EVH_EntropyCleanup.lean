import PV_EVH_HeapClear
set_option autoImplicit false
namespace PV_EVH_EntropyCleanup
open Aeneas Aeneas.Std PV_EVH_Runtime PV_EVH_HeapOwnership

/-- The original buffer key survives a partial fill. Rust's `?` drops the
Zeroizing array on an ordinary Err, including a partially overwritten buffer.
Abort/exhaustion are different: bind preserves the prefix without running glue. -/
def fillScope {E B : Type} (fill : Q (core.result.Result Unit E))
    (consume : Q (core.result.Result B E)) (dropBuffer : Q Unit) :
    Q (core.result.Result B E) := do
  let result ← fill
  match result with
  | .Err e => do
    let _ ← dropBuffer
    pure (.Err e)
  | .Ok _ => do
    let out ← consume
    let _ ← dropBuffer
    pure out

/-- No returned-error branch assumes the delivered prefix was empty. The
cleanup receives exactly the fill's post-state, with all partial writes. -/
theorem error_cleanup_world {E B : Type} (fill : Q (core.result.Result Unit E))
    (consume : Q (core.result.Result B E)) (dropBuffer : Q Unit)
    (w : State) (e : E) (h : (fill w).outcome = .returned (.ok (.Err e))) :
    fillScope fill consume dropBuffer w =
      let cleaned := PV_EVH_Runtime.bind dropBuffer
        (fun _ => PV_EVH_Runtime.lift (.ok (core.result.Result.Err (T := B) e))) (fill w).state
      ⟨cleaned.outcome,cleaned.state,(fill w).events ++ cleaned.events⟩ := by
  simp only [fillScope,Bind.bind,PV_EVH_Runtime.bind,h]

theorem cleanup_fault_prefix {E B : Type} (fill : Q (core.result.Result Unit E))
    (consume : Q (core.result.Result B E)) (dropBuffer : Q Unit)
    (w : State) (e : E) (fault : Fault)
    (h : (fill w).outcome = .returned (.ok (.Err e)))
    (hd : (dropBuffer (fill w).state).outcome = .fault fault) :
    fillScope fill consume dropBuffer w =
      ⟨.fault fault,(dropBuffer (fill w).state).state,
        (fill w).events ++ (dropBuffer (fill w).state).events⟩ := by
  simp only [fillScope,Bind.bind,PV_EVH_Runtime.bind,h,hd]

theorem abort_skips_cleanup {E B : Type} (fill : Q (core.result.Result Unit E))
    (consume : Q (core.result.Result B E)) (dropBuffer : Q Unit)
    (w : State) (fault : Fault) (h : (fill w).outcome = .fault fault) :
    fillScope fill consume dropBuffer w = ⟨.fault fault,(fill w).state,(fill w).events⟩ :=
  bind_fault _ _ _ _ h

/-- Drop uses the original owner/identity, not bytes returned by an external.
The native 64-byte stack mapping and zeroize::Zeroizing glue remain P work. -/
def dropEntropyBuffer (encode : PV_EVH_VolatileClear.Event → PV_RJ4IDB.Bytes)
    (key : Key) : Q Unit := PV_EVH_HeapClear.clearOwned encode key 64

#print axioms error_cleanup_world
#print axioms cleanup_fault_prefix
#print axioms abort_skips_cleanup
end PV_EVH_EntropyCleanup
