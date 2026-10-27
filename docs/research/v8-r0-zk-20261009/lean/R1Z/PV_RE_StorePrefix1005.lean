import R1Z.PV_RE_BindTransport10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_StorePrefix1005
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
/-- Actual ordered reservation prefix 5: all earlier native successes are explicit. -/
theorem prefix (store : Store) (statement nonce : Array U8 32#usize)
    (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written))
    (created : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h3 : std.fs.OpenOptions.create_new written.1 true = .ok (created))
    (moded : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h4 : std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 = .ok (moded)) :
    ∃ next, aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible store statement nonce =
      (std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path >>= next) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  change ∃ next, (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce >>= _) = _
  rw [h0]
  change ∃ next, (std.fs.OpenOptions.new >>= _) = _
  rw [h1]
  change ∃ next, (std.fs.OpenOptions.write options true >>= _) = _
  rw [h2]
  change ∃ next, (std.fs.OpenOptions.create_new written.1 true >>= _) = _
  rw [h3]
  change ∃ next, (std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 >>= _) = _
  rw [h4]
  exact ⟨_,rfl⟩
#print axioms prefix
end R1Z.PV_RE_StorePrefix1005
