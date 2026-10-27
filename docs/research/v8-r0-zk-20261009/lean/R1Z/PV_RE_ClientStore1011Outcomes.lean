import R1Z.PV_RE_ClientStore1011
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientStore1011Outcomes
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
theorem failure {C : Type} (ops : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (entropy_prefix : (EntropyWrapper (ProverRwOuterMapErr.selected ops) entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest binding : Array U8 32#usize)
    (serialization : (ProverRwOuterMapErr.selected ops).op226 pub = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (second_hash : hash (bindingFrame bytes 2#u8
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} secret.mask_nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written))
    (created : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h3 : std.fs.OpenOptions.create_new written.1 true = .ok (created))
    (moded : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h4 : std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 = .ok (moded))
    (file : std.fs.File) (h5 : std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path = .ok (.Ok file))
    (file1 : std.fs.File) (h6 : std.fs.File.Insts.StdIoWrite.write_all file (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC) = .ok ((.Ok (),file1)))
    (file2 : std.fs.File) (h7 : std.fs.File.Insts.StdIoWrite.write_all file1 (Array.to_slice digest) = .ok ((.Ok (),file2)))
    (file3 : std.fs.File) (h8 : std.fs.File.Insts.StdIoWrite.write_all file2 (Array.to_slice secret.mask_nonce) = .ok ((.Ok (),file3)))
    (h9 : std.fs.File.sync_all file3 = .ok (.Ok ()))
    (directory : std.path.Path) (h10 : std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref store.directory = .ok (directory)) (e : Error) (stopped : aspis_prover.state_only_entropy.sync_directory directory = .fail e),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .fail e := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro path h0 options h1 written h2 created h3 moded h4 file h5 file1 h6 file2 h7 file3 h8 h9 directory h10 e stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientStore1011.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash path h0 options h1 written h2 created h3 moded h4 file h5 file1 h6 file2 h7 file3 h8 h9 directory h10
  rw [stopped] at hn
  exact hn
#print axioms failure
theorem divergence {C : Type} (ops : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (entropy_prefix : (EntropyWrapper (ProverRwOuterMapErr.selected ops) entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest binding : Array U8 32#usize)
    (serialization : (ProverRwOuterMapErr.selected ops).op226 pub = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (second_hash : hash (bindingFrame bytes 2#u8
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} secret.mask_nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written))
    (created : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h3 : std.fs.OpenOptions.create_new written.1 true = .ok (created))
    (moded : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h4 : std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32 = .ok (moded))
    (file : std.fs.File) (h5 : std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path = .ok (.Ok file))
    (file1 : std.fs.File) (h6 : std.fs.File.Insts.StdIoWrite.write_all file (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC) = .ok ((.Ok (),file1)))
    (file2 : std.fs.File) (h7 : std.fs.File.Insts.StdIoWrite.write_all file1 (Array.to_slice digest) = .ok ((.Ok (),file2)))
    (file3 : std.fs.File) (h8 : std.fs.File.Insts.StdIoWrite.write_all file2 (Array.to_slice secret.mask_nonce) = .ok ((.Ok (),file3)))
    (h9 : std.fs.File.sync_all file3 = .ok (.Ok ()))
    (directory : std.path.Path) (h10 : std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref store.directory = .ok (directory)) (stopped : aspis_prover.state_only_entropy.sync_directory directory = .div),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .div := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro path h0 options h1 written h2 created h3 moded h4 file h5 file1 h6 file2 h7 file3 h8 h9 directory h10 stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientStore1011.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash path h0 options h1 written h2 created h3 moded h4 file h5 file1 h6 file2 h7 file3 h8 h9 directory h10
  rw [stopped] at hn
  exact hn
#print axioms divergence
end R1Z.PV_RE_ClientStore1011Outcomes
