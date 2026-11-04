import R1Z.ProverCommitTapeCompletion
import R0Z.FsAbortTape

/-! Exact finite measure transport for the H1 quotient. The completion input
contains explicit padding randomness. No source-stream law is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0Z.JointView R0Z.MaskLayout R0Z.FsAbortBounds R0P
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Fintype K] {F : Subfield K}

/-- Uniform independent quotient and padding complete to the uniform full tape. -/
theorem completion_mass (event : Tape K F → Prop) :
    mass (fun s : SourceTape K F × Padding K F => event (complete s.1 s.2)) =
      mass event := by
  exact (mass_equiv (completionEquiv (K := K) (F := F)).symm event).symm

/-- Uniform full-tape projection is uniform on the quotient. -/
theorem quotient_mass (event : SourceTape K F → Prop) :
    mass (fun t : Tape K F => event (project t)) = mass event := by
  rw [← completion_mass]
  simp only [project_complete]
  haveI : Nonempty (Padding K F) := ⟨fun _ => 0⟩
  exact R0Z.FsAbortTape.mass_fst event

/-- Every observable factoring through the quotient has exactly the same law
under any deterministic representative, including zero fill. This is a law
of observables, not uniformity of the completed raw tape. -/
theorem observable_mass {O : Type} (observe : Tape K F → O)
    (invariant : ∀ t h, observe (complete (project t) h) = observe t)
    (choose : SourceTape K F → Padding K F) (event : O → Prop) :
    mass (fun s : SourceTape K F => event (observe (complete s (choose s)))) =
      mass (fun t : Tape K F => event (observe t)) := by
  rw [← quotient_mass (fun s => event (observe (complete s (choose s))))]
  exact mass_congr _ _ (fun t => by rw [invariant])

/-- Ordinary mask columns are retained by the quotient. -/
theorem maskOnly_completion (t : Tape K F) (h : Padding K F) (c : Fin 10) :
    maskOnlyColumns (Sum.elim t.2 (complete (project t) h).1) c =
      maskOnlyColumns (Sum.elim t.2 t.1) c := by
  unfold maskOnlyColumns maskOnlyRaw
  congr 1
  funext r
  exact congrArg (fun v : F => (v : K)) (dif_neg (show ¬ Ignored (.inl (c,r)) from not_false))

/-- G and D are retained at every raw coordinate. -/
theorem extension_completion (B : PackBasis F) (t : Tape K F)
    (h : Padding K F) (lane : Fin 3) (hl : lane ≠ 1) :
    extensionRaw B (Sum.elim t.2 (complete (project t) h).1) lane =
      extensionRaw B (Sum.elim t.2 t.1) lane := by
  funext r
  unfold extensionRaw
  congr 1
  funext limb
  exact congrArg (fun v : F => (v : K)) (dif_neg (fun bad => hl bad.1))

/-- The model affine trace construction factors through the H1 quotient. -/
theorem applyAff_completion (B : PackBasis F) (trace : Trace K)
    (t : Tape K F) (h : Padding K F) :
    applyAff B trace (complete (project t) h).1 = applyAff B trace t.1 := by
  funext c r
  simp only [applyAff]
  split_ifs
  · rfl
  · exact congrFun (maskOnly_completion (t.1, 0) h _) r
  · exact congrArg (fun x => trace c r + x) (congrFun (h1_completion B (t.1, 0) h) r)
  · exact congrFun (congrArg (balance 0)
      (extension_completion B (t.1, 0) h 0 (by decide))) r
  · exact congrFun (congrArg (balance 0)
      (extension_completion B (t.1, 0) h 2 (by decide))) r

#print axioms completion_mass
#print axioms quotient_mass
#print axioms observable_mass
#print axioms maskOnly_completion
#print axioms extension_completion
#print axioms applyAff_completion
end R1Z.ProverCommitTapeCompletion
