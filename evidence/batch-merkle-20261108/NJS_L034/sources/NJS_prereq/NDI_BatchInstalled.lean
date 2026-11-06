import NDI_BatchCaller
import NDI_BatchControl
set_option autoImplicit false
namespace NDI_BatchInstalled
open Aeneas Aeneas.Std Result AspisR1

theorem installed (raw : Array U32 22#usize) (lo n tree : Usize)
    (split : (lo=0#usize ∧ n=10#usize) ∨ (lo=10#usize ∧ n=12#usize))
    (kind : tree.val<3) (canonical : ∀ k, k<22 → raw.val[k]!.val<262144) :
    NDI_BatchRef.batch_keys_ref raw lo n tree=Port4B_KeyInstall.build raw lo n tree := by
  rcases split with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rw [NDI_BatchBridge.reference raw 0#usize 10#usize tree 0 rfl rfl canonical]
    simp [Port4B_KeyInstall.build,OraclePortSelectedDraft.batchPositions,kind]
  · rw [NDI_BatchBridge.reference raw 10#usize 12#usize tree 1 rfl rfl canonical]
    simp [Port4B_KeyInstall.build,OraclePortSelectedDraft.batchPositions,kind]

#print axioms installed
end NDI_BatchInstalled
