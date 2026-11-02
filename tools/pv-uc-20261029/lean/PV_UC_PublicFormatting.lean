import Aeneas

/- Privacy needs congruence of a deterministic renderer, not a model of text.
   These renderers are explicit parameters, not global axioms or installed
   implementations of the entry's still-unbound external operations. -/
namespace PV_UC_PublicFormatting

structure Renderers (Json Key : Type) where
  fdPath : Int → String
  stdoutJson : Json → String
  pubkey : Key → String

-- Exactly the public integer argument of wallet.rs's format! call.
def walletPath {Json Key : Type} (r : Renderers Json Key)
    (publicFd : Int) : String := r.fdPath publicFd

theorem walletPath_same_public {Json Key : Type} (r : Renderers Json Key)
    (fd₁ fd₂ : Int) (h : fd₁ = fd₂) : walletPath r fd₁ = walletPath r fd₂ := by
  cases h
  rfl

-- A public transcript must already have been simulated before serialization.
-- This premise is not a proof that the client's constructed Value is public.
theorem stdout_recomputable {Json Key : Type} (r : Renderers Json Key)
    (actual simulated : Json) (h : actual = simulated) :
    r.stdoutJson actual = r.stdoutJson simulated := by
  cases h
  rfl

theorem pubkey_recomputable {Json Key : Type} (r : Renderers Json Key)
    (actual simulated : Key) (h : actual = simulated) :
    r.pubkey actual = r.pubkey simulated := by
  cases h
  rfl

-- The clock is an additional input, not a consequence of the request.
-- This isolates the honest-run obligation for the actual Number::from_f64
-- call; no witness-independence law for elapsed is postulated here.
def elapsedArgument {Public Witness : Type} (elapsed : Public → Witness → Nat)
    (p : Public) (w : Witness) : Nat := elapsed p w

theorem elapsed_public_iff {Public Witness : Type}
    (elapsed : Public → Witness → Nat) :
    (∀ p w₁ w₂, elapsedArgument elapsed p w₁ = elapsedArgument elapsed p w₂) ↔
    (∀ p w₁ w₂, elapsed p w₁ = elapsed p w₂) := by
  rfl

#print axioms walletPath_same_public
#print axioms stdout_recomputable
#print axioms pubkey_recomputable
#print axioms elapsed_public_iff
end PV_UC_PublicFormatting
