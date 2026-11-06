import NJJ_Cuts
import NJJ_RowWindow
set_option autoImplicit false
noncomputable section
namespace NJJ_Pending
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Row := Port3_NativePendingBody.Row
abbrev K := aspis_core.field.QM31

/-- Finite induction over the reviewed ONE-row native cuts. These hypotheses
are step transcriptions, not final-vector or successful-child equations.
The native allocation/error start and final ownership cuts stay separate. -/
theorem windows (weights : Slice K) (size : weights.val.length=64)
 (states : Nat → alloc.vec.Vec Row)
 (cuts : ∀ i, i<64 → NJJ_Cuts.pendingStep weights (states i) (states (i+1)) i (i+1)) :
 (states 64).val=weights.val.map Port3_PendingInstall.row := by
 have invariant : ∀ n, n≤64 → Port3_NativePendingLoop.Prefix weights (states n) n := by
  intro n
  induction n with
  | zero => intro _ j impossible;omega
  | succ n ih =>
    intro bound j inside
    have step:=cuts n (by omega)
    change (states (n+1)).val[j]?=(weights.val[j]?).map Port3_PendingInstall.row
    rw [step.2.2 j (by omega)]
    by_cases same : n=j
    · subst j;rw [if_pos rfl]
    · rw [if_neg same]
      exact ih (by omega) j (by omega)
 have finalSize : (states 64).val.length=64 := (cuts 63 (by omega)).2.1
 exact Port3_NativePendingLoop.complete weights (states 64) size finalSize (invariant 64 (by omega))

/-- Source/model association of the native loop's complete payload. The
allocator result is still the SAME-site primitive outcome; this theorem does
not substitute a fresh Bool for the runtime allocator item. -/
theorem source (reserved : Bool) (weights : Slice K) (size : weights.val.length=64)
 (states : Nat → alloc.vec.Vec Row)
 (cuts : reserved=true → ∀ i, i<64 → NJJ_Cuts.pendingStep weights (states i) (states (i+1)) i (i+1)) :
 Port3_NativePendingInstall.source reserved weights=
 if reserved then ok (.Ok (⟨states 64,0#usize⟩ : verifier.BatchedWeights)) else ok (.Err .Allocation) := by
 unfold Port3_NativePendingInstall.source
 rw [Port3_NativePendingInstall.emitted_exact reserved weights size]
 cases h:reserved with
 | false => rfl
 | true =>
   have cells:=windows weights size states (cuts h)
   have same : states 64=Port3_PendingInstall.raw weights := by
    apply Subtype.ext
    exact cells
   rw [same]
   rfl

#print axioms windows
#print axioms source
end NJJ_Pending
