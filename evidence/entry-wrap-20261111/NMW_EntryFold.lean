import NMW_Fold
set_option autoImplicit false
noncomputable section
namespace NMW_EntryFold
open Aeneas Aeneas.Std Result AspisR1 NMW_Outcome NMW_FullDispatch NMW_RowSpecs
/-- The REAL direct child of lib.rs entry is process, at identical arguments.
No RefCell guard is held in this deployed cfg arm. -/
theorem admitted {A W E : Type} (children : Children A W E)
 (input : Args A) (before : W) (release : Release input.data) :
 entry children input before = process children input before := by
 rw [entry,NMW_Symbolic.entry,Hiq_DispatchAdmitted.exact]
 rcases release with one | two
 · simp only [one,true_or,ite_true]
   rfl
 · simp only [two,or_true,ite_true]
   rfl
/-- Compile-once one-line entry instantiation after the process child closes.
This is an intermediate fold; the process packet is not a root hypothesis. -/
theorem from_process {A W E : Type} (native model : Children A W E)
 (domain : Args A → W → Prop) (processPacket : ProcessSpec native model domain) :
 EntrySpec native model domain := by
 intro input before own
 by_cases release : Release input.data
 · rw [admitted native input before release,admitted model input before release]
   exact processPacket input before own release
 · have noFirst : ¬ Hiq_ReleaseRoute.stage1 input.data := fun h => release (Or.inl h)
   have noSecond : ¬ Hiq_ReleaseRoute.asq8 input.data := fun h => release (Or.inr h)
   have rejected : Hiq_ReleaseRoute.route input.data = .reject := by
     simp [Hiq_ReleaseRoute.route,noFirst,noSecond]
   rw [entry_total,entry_total,rejected]
/-- Both owned process occurrences and both entry occurrences compose in one
fold over the actual shared call structure. Instantiation awaits NMV roots. -/
theorem combined {A W E : Type} (native model : Children A W E)
 (parentDomain firstDomain secondDomain : Args A → W → Prop)
 (stage1 : RowSpec_344 native.first model.first firstDomain)
 (stage2 : RowSpec_240 native.second model.second secondDomain)
 (caller1 : CallerClause Hiq_ReleaseRoute.stage1 parentDomain firstDomain)
 (caller2 : CallerClause Hiq_ReleaseRoute.asq8 parentDomain secondDomain) :
 ProcessSpec native model parentDomain ∧ EntrySpec native model parentDomain := by
 have processPacket := NMW_Fold.process_fold native model parentDomain firstDomain secondDomain
   stage1 stage2 caller1 caller2
 exact ⟨processPacket,from_process native model parentDomain processPacket⟩
#print axioms admitted
#print axioms from_process
#print axioms combined
end NMW_EntryFold
end
