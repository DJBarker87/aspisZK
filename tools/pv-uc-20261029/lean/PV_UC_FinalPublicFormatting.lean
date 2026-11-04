import Aeneas
import PVUCReadyEntry.Funs

/- Privacy needs congruence of a deterministic renderer, not a model of text.
   These renderers are explicit parameters, not global axioms or installed
   implementations of the entry's still-unbound external operations. -/
namespace PV_UC_FinalPublicFormatting

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

-- Distinct native effect interpretations may read different private records.
-- Only the pure formatter is shared; no equality of the entire effect record
-- is assumed. Binding laws are explicit P obligations, never global axioms.
theorem extracted_fd_formatter_public
    [types : PV_UC_ReadyEntry.ExternalTypes]
    (left right : PV_UC_ReadyEntry.ExternalFuns)
    (format : Aeneas.Std.I32 → Aeneas.Std.Result _root_.String)
    (bindLeft : ∀ x, @PV_UC_ReadyEntry.wallet_fd_path types left x = format x)
    (bindRight : ∀ x, @PV_UC_ReadyEntry.wallet_fd_path types right x = format x)
    (fd₁ fd₂ : Aeneas.Std.I32) (h : fd₁ = fd₂) :
    @PV_UC_ReadyEntry.wallet_fd_path types left fd₁ =
    @PV_UC_ReadyEntry.wallet_fd_path types right fd₂ := by
  rw [bindLeft, bindRight, h]

theorem extracted_json_formatter_recomputable
    [types : PV_UC_ReadyEntry.ExternalTypes]
    (left right : PV_UC_ReadyEntry.ExternalFuns)
    (format : PV_UC_ReadyEntry.serde_json.value.Value → Aeneas.Std.Result _root_.String)
    (bindLeft : ∀ x, @PV_UC_ReadyEntry.render_json types left x = format x)
    (bindRight : ∀ x, @PV_UC_ReadyEntry.render_json types right x = format x)
    (actual simulated : PV_UC_ReadyEntry.serde_json.value.Value)
    (h : actual = simulated) :
    @PV_UC_ReadyEntry.render_json types left actual =
    @PV_UC_ReadyEntry.render_json types right simulated := by
  rw [bindLeft, bindRight, h]

theorem extracted_pubkey_formatter_recomputable
    [types : PV_UC_ReadyEntry.ExternalTypes]
    (left right : PV_UC_ReadyEntry.ExternalFuns)
    (format : PV_UC_ReadyEntry.solana_pubkey.Pubkey → Aeneas.Std.Result _root_.String)
    (bindLeft : ∀ x, @PV_UC_ReadyEntry.pubkey_text types left x = format x)
    (bindRight : ∀ x, @PV_UC_ReadyEntry.pubkey_text types right x = format x)
    (actual simulated : PV_UC_ReadyEntry.solana_pubkey.Pubkey)
    (h : actual = simulated) :
    @PV_UC_ReadyEntry.pubkey_text types left actual =
    @PV_UC_ReadyEntry.pubkey_text types right simulated := by
  rw [bindLeft, bindRight, h]

#print axioms walletPath_same_public
#print axioms stdout_recomputable
#print axioms pubkey_recomputable
#print axioms extracted_fd_formatter_public
#print axioms extracted_json_formatter_recomputable
#print axioms extracted_pubkey_formatter_recomputable
end PV_UC_FinalPublicFormatting
