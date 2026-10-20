import Query31ExplicitListLoop
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ArrayScanValid
open Query31ExplicitListLoop Query31ExplicitScanBody AspisV8R19.Q22WordScan

def arrayIteratorModel {n : Usize} (a : Array Std.U32 n) : List Std.U32 := a.val

/-- Array-order list semantics preserve the scanner invariant as well as the
    Q22 state transition. The invariant is what permits the next source block
    to be scanned without an independent per-block bound premise. -/
theorem array_scan_q22_valid {n : Usize} (a : Array Std.U32 n)
    (s : Query31ExplicitListLoop.CurrentScan) (hs : validState s) :
    ∃ sf pending,
      scanListLoop (arrayIteratorModel a) s = .ok (sf, pending) ∧
      scan (q22StateOf s) (a.val.map (fun x => x.val)) =
        (q22StateOf sf, optionStop pending) ∧
      validState sf := by
  obtain ⟨sf, pending, hloop, hscan, hvalid⟩ :=
    scanListLoop_q22_valid (arrayIteratorModel a) s hs
  exact ⟨sf, pending, hloop, hscan, hvalid⟩

#print axioms array_scan_q22_valid
end Query31ArrayScanValid
