import PV_L1D_CallbackSafe
import PV_L1E_OwnerJoin
import PV_RJ4IDB_OpenInputs
set_option autoImplicit false
namespace PV_L1E_ErasureObstruction
open Aeneas Aeneas.Std Result
open PV_L1D_Logged PV_L1D_CallbackSafe

/-- A model counterexample to deriving entry-log equality from complete Result
erasure. This is not an honest-native leak or a witness-dependent execution. -/
theorem result_erasure_does_not_determine_entries :
    ∃ x y : Logged Unit, erase x = erase y ∧ callbacks x.events ≠ callbacks y.events := by
  refine ⟨⟨[],.ok ()⟩,⟨[.call .callback 0],.ok ()⟩,rfl,?_⟩
  intro impossible
  cases impossible
#print axioms result_erasure_does_not_determine_entries

/-- D163's original total owner cannot encode an outer failure by equality
with its lifted record. The outer-error prefix needs an additional runtime
association; silently identifying it with a normal D163 stop is invalid. -/
theorem outer_failure_not_total_owner {S P : Type}
    (a : PV_L1D_RetryFold.Attempt S P) (s : S) (k : Nat)
    (e : Aeneas.Std.Error) (failed : (a k s).result = .fail e) :
    ¬ ∃ owner : R1Z.SideChannelL1AttemptRecord.Owner S P,
      PV_L1E_OwnerJoin.PV_L1E_Link_SourceOwner a owner := by
  rintro ⟨owner,link⟩
  have same := congrArg Logged.result (link k s)
  rw [failed] at same
  cases step : owner k s with
  | mk record after =>
    simp only [PV_L1E_OwnerJoin.liftOwner,step] at same
    cases same
#print axioms outer_failure_not_total_owner

/-- Independent native traces can have the same terminal value and different
COUNT projections. Output agreement alone cannot manufacture a producer law. -/
theorem native_output_does_not_determine_count :
    ∃ x y : PV_RJ4IDB.NativeTrace Unit,
      x.terminal = y.terminal ∧
      PV_RJ4IDB.nativeCounts x.events ≠ PV_RJ4IDB.nativeCounts y.events := by
  refine ⟨⟨[],.success ()⟩,⟨[.count 1],.success ()⟩,rfl,?_⟩
  intro impossible
  cases impossible
#print axioms native_output_does_not_determine_count
end PV_L1E_ErasureObstruction
