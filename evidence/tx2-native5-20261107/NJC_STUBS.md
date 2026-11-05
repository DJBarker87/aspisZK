# NJC stubs

No field multiplication stub, function contract, stub_verified call, writable static or Option<fn>-dependent assertion is introduced. No SHA/syscall body is unwound.

NJC Reader harnesses use only the exact KMX_copy_nonoverlapping and KMX_copy_from_slice from evidence/kani-mitig-20261028/KMX_copy_stubs.patch (sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67). KMX_stubs.rs, KMX_native.rs and KMX_CopyMeaning.lean hashes are checked before every run. These are supplied copy-mitigation stubs, not new worker-defined copy semantics. A passing copy-dependent native law will require its matched failing control in the same configuration; no unchecked/timeout result is credited.

Caller domains are bounded Reader input1768 with arbitrary pre-cursor such that the entire read fits. This covers all literal resume read offsets; it does not establish the upstream header/proof/public/heap producer association by itself. Full backing content frames are proved from the emitted raw source; pointer equality alone is never lifted to byte equality.
