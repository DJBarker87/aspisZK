import NMP_ObservedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedStoppedPrefix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_ObservedSteps
open NMT_CallTree (run Event)
theorem abort {H W : Type} (c : Calls) (s : Parent H W) (e : Error)
 (h : c.c6 s.bytes = .fail e) :
 run (body c s) = (.fail e,[Event.call "TX1:138/parse" s.bytes
  (.fail e : Result (core.result.Result r1_wire.Prefix r1_wire.Error))]) := by
 unfold body
 rw [execute]
 unfold step
 rw [h]
 rfl
theorem diverge {H W : Type} (c : Calls) (s : Parent H W)
 (h : c.c6 s.bytes = .div) :
 run (body c s) = (.div,[Event.call "TX1:138/parse" s.bytes
  (.div : Result (core.result.Result r1_wire.Prefix r1_wire.Error))]) := by
 unfold body
 rw [execute]
 unfold step
 rw [h]
 rfl
#print axioms abort
#print axioms diverge
end AspisR1.NMP_ObservedStoppedPrefix
