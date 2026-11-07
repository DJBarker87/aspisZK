import NMM_LaneScalarSource
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_PayloadComponents
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
abbrev Fields := NMM_LaneScalarSource.Fields
abbrev PE := NMM_LaneScalarSource.PE

def metadata (a : Fields) := (a.bump,a.master,a.lane,a.next)

def view {α : Type} (f : Fields → α) : core.result.Result Fields PE → core.result.Result α PE
 | .Err e => .Err e
 | .Ok value => .Ok (f value)

/-- Separate native observations must all refer to the same complete outcome.
No component alone is promoted to a payload or returning-outcome certificate. -/
theorem fields_complete (a b : Fields) (meta : metadata a = metadata b)
 (root : a.root=b.root) (frontier : a.frontier=b.frontier) : a=b := by
 cases a
 cases b
 simp_all [metadata]

theorem result_complete (a b : core.result.Result Fields PE)
 (meta : view metadata a = view metadata b)
 (root : view Fields.root a = view Fields.root b)
 (frontier : view Fields.frontier a = view Fields.frontier b) : a=b := by
 cases a with
 | Err e =>
  cases b with
  | Err f => exact congrArg core.result.Result.Err (core.result.Result.Err.inj meta)
  | Ok value => cases meta
 | Ok value =>
  cases b with
  | Err e => cases meta
  | Ok other =>
   exact congrArg core.result.Result.Ok (fields_complete value other
    (core.result.Result.Ok.inj meta) (core.result.Result.Ok.inj root) (core.result.Result.Ok.inj frontier))

#print fields_complete
#print axioms fields_complete
#print result_complete
#print axioms result_complete
end NMM_PayloadComponents
