import NNU_GeometryCallbacks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryIndex
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody

theorem map_error {C : Type} (f : core.ops.function.FnOnce Unit C AspisR1Stage2.verifier.Error)
 (law : ∀ e, f.call_once () e = .ok .Query) (reply : core.result.Result Usize C) :
 Port4C_GeometryStd.mapError f reply () = NNH_Run5bIndexLaw.erase (.ok reply) := by
 cases reply <;> simp only [Port4C_GeometryStd.mapError,law,bind_tc_ok,NNH_Run5bIndexLaw.erase]

theorem mapped {C : Type} (g : Ops C) (u : Usize)
 (f : core.ops.function.FnOnce Unit C AspisR1Stage2.verifier.Error)
 (law : ∀ e, f.call_once () e = .ok .Query) :
 (do let reply ← g.op12 u; Port4C_GeometryStd.mapError f reply ()) =
 NNH_Run5bIndexLaw.erase (g.op12 u) := by
 unfold NNH_Run5bIndexLaw.erase
 apply bind_congr
 intro reply
 exact map_error f law reply

theorem after_map {C A : Type} (g : Ops C) (u : Usize)
 (f : core.ops.function.FnOnce Unit C AspisR1Stage2.verifier.Error)
 (law : ∀ e, f.call_once () e = .ok .Query)
 (k : core.result.Result Usize AspisR1Stage2.verifier.Error → Result A) :
 (do let reply ← g.op12 u; let mapped ← Port4C_GeometryStd.mapError f reply (); k mapped) =
 (do let mapped ← NNH_Run5bIndexLaw.erase (g.op12 u); k mapped) := by
 cases indexRun : g.op12 u with
 | fail e => rfl
 | div => rfl
 | ok reply =>
  simp only [bind_tc_ok,NNH_Run5bIndexLaw.erase]
  rw [map_error f law reply]
  cases reply <;> rfl
#print axioms map_error
#print axioms mapped
#print axioms after_map
end AspisR1.NNU_GeometryIndex
end
