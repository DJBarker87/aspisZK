# NIZ stubs and trust boundary

Exact KMX_copy_stubs.patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 is applied in every native run with the retained attribute list. No own copy implementation, multiplication/hash stub, function contract, stub_verified, writable static or function-pointer-value observation is introduced. Copy-dependent credit requires the matched failing control.

| Stub | Named theorem and domain | Disposition |
|---|---|---|
| NIZ_eq, replacing Pubkey::eq in K009/K010 and K023..K026 | NIZ_KeyEquality.memcmp_eq_spec/spec_key_eq, NIZ_Memcmp.zero_iff/key32_zero, NIZ_AliasWindow.transport_cut; exactly 32 readable byte observations of valid Pubkey references. K021/K022 supplies the actual one-window typed key view. | Mathematical fixed32 spec and host-byte zero/frame laws are checked. The complete original generated Pubkey::eq/native-loop/source association remains OPEN. These caller passes are CONDITIONAL, not source/native callee closures. No emitted-definition theorem is invented. |
| Exact KMX copy/alloc primitives | Existing KMX_CopyMeaning laws, retained by hash; exact original patch and attributes in every receipt. | Reused; no own copy stub. Actual parent/copy/source domain remains per-call. |

Native direct one-byte memcmp checks K004..K008 concern CBMC 6.8's host builtin, whose generic loop body is retained by L011. They do not extend the Solana RuntimeMemcmp row. Under ruling (ac) that accepted row remains the SAME readable 688-byte-range zero/frame contract, never a generic 32-byte syscall assumption.

Pool admission uses exactly AdapterRw.RuntimeEntrypointAdmission under (ap), with all seven fields unchanged. RuntimeCpiReadonlyEntry7 is PENDING and unused. Native contract semantic transport/reviewed transcription remains P6/D188 option-A reclassification, never a removed premise. Std, allocator, ABI/compiler, data-only S2TrustedSdkBorrow and source-to-ELF transport remain retained. Rc clone/free, lamport wrappers, assign, resize and CPI/callback source frames are not silently covered by the fifteen data-borrow fields. No new trust row is adopted.
