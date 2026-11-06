import NLM_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLF_RefCell NLF_SdkModel
/-- Normal-return state. Payload, accounts and cell ownership all restore;
only the ghost token allocator and owned list advance. -/
def returned (s : State) (a lo hi : Nat) : State :=
 {s with next:=s.next+1,owned:=s.owned++[s.input.snapshot a lo hi]}
theorem normal_result (e : Entry) (t a lo hi : Nat) (owned : List Owned) :
 (G (ready e t owned) a lo hi (.ok ())).result =
 .ok (e.snapshot a lo hi,returned (ready e t owned) a lo hi) := by
 unfold G
 rw [acquire]
 simp only [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_pure,NJU_Log.erase_if,bind_tc_ok]
 rw [release_current]
 split <;>
  simp [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_pure,
    NJU_Log.erase_liftM,NJU_Log.erase_if,bind_tc_ok,returned,ready]

#print normal_result
#print axioms normal_result
end NLM_Snapshot
