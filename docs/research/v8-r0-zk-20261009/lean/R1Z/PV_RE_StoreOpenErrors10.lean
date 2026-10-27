import R1Z.PV_RE_BindTransport10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_StoreOpenErrors10
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
/-- Actual ordered reservation prefix 5: all earlier native successes are explicit. -/
theorem already_exists (store : Store) (statement nonce : Array U8 32#usize)
    (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written))
    (created : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h3 : std.fs.OpenOptions.create_new written.1 true = .ok (created))
    (moded : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h4 : std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 = .ok (moded))
    (error : std.io.error.Error) (kind : core.io.error.ErrorKind)
    (opened : std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path = .ok (.Err error))
    (classified : std.io.error.Error.kind error = .ok kind)
    (compared : core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind core.io.error.ErrorKind.AlreadyExists = .ok true)) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible store statement nonce = .ok (.Ok false,{store with last_error := none}) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  change (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce >>= _) = _
  rw [h0]
  change (std.fs.OpenOptions.new >>= _) = _
  rw [h1]
  change (std.fs.OpenOptions.write options true >>= _) = _
  rw [h2]
  change (std.fs.OpenOptions.create_new written.1 true >>= _) = _
  rw [h3]
  change (std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 >>= _) = _
  rw [h4]

  change (std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path >>= _) = _
  rw [opened]
  change (std.io.error.Error.kind error >>= _) = _
  rw [classified]
  change (core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind core.io.error.ErrorKind.AlreadyExists >>= _) = _
  rw [compared]
  rfl
#print axioms already_exists
theorem other_error (store : Store) (statement nonce : Array U8 32#usize)
    (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written))
    (created : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h3 : std.fs.OpenOptions.create_new written.1 true = .ok (created))
    (moded : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h4 : std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 = .ok (moded))
    (error : std.io.error.Error) (kind : core.io.error.ErrorKind)
    (opened : std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path = .ok (.Err error))
    (classified : std.io.error.Error.kind error = .ok kind)
    (compared : core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind core.io.error.ErrorKind.AlreadyExists = .ok false)) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible store statement nonce = .ok (.Err error,{store with last_error := none}) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  change (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce >>= _) = _
  rw [h0]
  change (std.fs.OpenOptions.new >>= _) = _
  rw [h1]
  change (std.fs.OpenOptions.write options true >>= _) = _
  rw [h2]
  change (std.fs.OpenOptions.create_new written.1 true >>= _) = _
  rw [h3]
  change (std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 >>= _) = _
  rw [h4]

  change (std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path >>= _) = _
  rw [opened]
  change (std.io.error.Error.kind error >>= _) = _
  rw [classified]
  change (core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind core.io.error.ErrorKind.AlreadyExists >>= _) = _
  rw [compared]
  rfl
#print axioms other_error
end R1Z.PV_RE_StoreOpenErrors10
