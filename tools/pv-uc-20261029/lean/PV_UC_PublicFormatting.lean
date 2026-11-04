import Aeneas
import PVUCStringEntry.Funs

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

-- The actual emitted call now retains the I32 operand. Source data-flow
-- checks establish that this operand is parsed only from public q, before
-- the first private record read. No text semantics or Unit fmt carrier used.
theorem extracted_fd_formatter_public
    [PV_UC_StringEntry.ExternalTypes] [PV_UC_StringEntry.ExternalFuns]
    (fd₁ fd₂ : Aeneas.Std.I32) (h : fd₁ = fd₂) :
    PV_UC_StringEntry.wallet_fd_path fd₁ = PV_UC_StringEntry.wallet_fd_path fd₂ := by
  cases h
  rfl

-- This is the actual String-rendering operation, with its Value retained.
-- Public/simulated equality is an explicit hypothesis; the clock field's
-- missing native witness-independence proof is not hidden in the renderer.
theorem extracted_json_formatter_recomputable
    [PV_UC_StringEntry.ExternalTypes] [PV_UC_StringEntry.ExternalFuns]
    (actual simulated : PV_UC_StringEntry.serde_json.value.Value)
    (h : actual = simulated) :
    PV_UC_StringEntry.render_json actual = PV_UC_StringEntry.render_json simulated := by
  cases h
  rfl

#print axioms walletPath_same_public
#print axioms stdout_recomputable
#print axioms pubkey_recomputable
#print axioms extracted_fd_formatter_public
#print axioms extracted_json_formatter_recomputable
end PV_UC_PublicFormatting
