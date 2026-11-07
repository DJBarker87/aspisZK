import PCM_Witness
import PCM_StepLaws
import PCM_Carriers
import PCM_SdkOps
set_option autoImplicit false
namespace PCM_POOL_333
open RSL PCM PCM.Computation
abbrev Args := AccountInfo × B32 × Nat × PCM.Rent
structure Children where
  programAccount : Child (AccountInfo × B32 × Bool) Unit
  rentExempt : PCM.Rent → UInt64 → Nat → Bool
/-- Lamports' infallible borrow is reached only after byte checks, and while
the data guard is live. Both kinds of cell identity remain explicit. -/
def Ref (C : Children) (a : Args) : Computation Unit := do
  let (account,program,n,rent) := a
  C.programAccount.call (account,program,true)
  guardScope account .shared fun _ => do
    let s ← get
    let data := s.bytes account
    check (data.length != n || data.any (· != 0)) (.custom 0x41532035)
    let lamports ← readLamports account
    check (!C.rentExempt rent lamports n) (.custom 0x41532035)
def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) (a : Args)
    (early : C.programAccount.call (a.1,a.2.1,true) = Computation.throw .invalidAccountData) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a .invalidAccountData .invalidArgument trivial
  · rcases a with ⟨account,program,n,rent⟩
    unfold Ref
    dsimp only at early ⊢
    rw [early]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_333
