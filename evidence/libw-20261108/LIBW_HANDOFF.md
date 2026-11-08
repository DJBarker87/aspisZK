# LIBW host handoff for ledger30

TGB-1: **RESOLVED** (registration obligation only). LIBW_WeakPerEnv compiled
UNCHANGED, passed raw ax2 on all19 exported roots, standard axioms only, and kept
all statements. No ledger row closes; no_row_status_depends_on_it: true.
TOP:G1b/TOP:G2 retain their separate actual top/runtime/source obligations.

TGB-1b: **RESOLVED_SEPARATE_HEADER_MODEL**. NNP_SeparateHeader.okHeader and
okHeader_any consume the SAME weak observation at the SAME Env, with no oracle
or repartitioning premise. canonical_header derives this from the canonical
native law's own domain/invocation/Bound064/TraceOf hypotheses on returned
success. The two header values use LIBB_HashModel.H env (singleton calls), while
the law's C04 model remains LIBB_PartitionEnv.H env. NNP_InstallField.header_identity
is rfl with the existing host NNH_G1aEnv.header, and field reuses the merged
host field at that signature. No new HostRep/HostRepAny premise or trust item.
The stronger original LIBW C04-valued header theorem remains conditional on its
OracleEnv; NNP_ResumeHeader isolates the exact two-value HeaderAgreement it
would require. No unconditional identification of the two hash models is claimed.

TGB-6 deliverable: **NNP_G2.frame_env** (also frame_any, weak240_env/any and
sdk_env/any). NNP_Weak241.fold_env/fold_any re-specialise merged NMS_R2Weak241.
Child RowSpec/representation/allocation/PoolLaws assumptions are retained,
not discharged by wrappers. See NNP_STAGE3.md for exact specialisation details.

NNP_HostIdentity.host_law proves wEnv NNH_064Install.frame =
AspisR1.NNH_064WeakField.w by rfl. NNP_InstallField.any_host_law proves wAny Unit
is equal to it. TGB-1 world caveat: canonical native quantifies over world;
wEnv fixes one syntactically. world_independent uses merged native world
transport to preserve End, trace and observation across any two frames. This
is not a physical headline World or source/native/runtime association claim.

## Compiled modules

Source/olean SHA-256 and exact scope receipts follow. All proof roots have both
#print axioms and raw ax2 audits in NNP_FINAL_proof0/1 (44 roots total), all within
{propext, Classical.choice, Quot.sound}. Validation utilities are not theorems.
Full target/command/exit/wall/peakRSS/swap/revision/dependency/axiom fields are in
../libw-host-20261108/NNP_COMPILE.tsv and NNP_MODULES.json.

| Module | Source SHA-256 | Olean SHA-256 | Scope receipt |
|---|---|---|---|
| LIBW_WeakPerEnv | fb8b8f99d667300639817a017433c40dc08ba0e7bb9bdfc437e5bda84420aacd | 07044e1f65ef4344a40b56d4b2ce23cbe94578ca53e9cd94fbb3fe3dd3837e78 | NNP_L001/receipt.json |
| NNP_ResumeHeader | 885e980a045dd775bc744030f22c89fbcd51e0d355dd852ef978ed60bcea9ad1 | 80befb8cb85aa4891c8d415e86f90f0144d910a99bdb49ae483747876c5e681c | NNP_L003/receipt.json |
| NNP_Weak241 | c7f7440e10a0e8cdf835273c82b39b6c02ea3c442ab2a94ad3307ab7ea803e88 | 75dd201288775ff1d37e03402e926d2a254071ff39d1328ae8f4797837aaff22 | NNP_L006/receipt.json |
| NNP_G2 | 039a08b99ba14bdf31e801c1240f9f1227594210bcb7fb7784b7600306d93d1a | 18c4342cdfed367795f8dcfc15533e5448e027d75a0455c8ebdaac2a99dbb820 | NNP_L007/receipt.json |
| NNP_HostIdentity | efe2fbcb83bac23e0669e058b29b99d48ea1b9cc1061f8f125177a4a87eea09f | 2b8da31613ee9655434d795f03d1f6140f491d6e2841d587d95f2d7351a2ce51 | NNP_L008/receipt.json |
| NNP_SeparateHeader | c1c651541a92e1896accae8d853db20d91d9f97e4edc2a5609f47d402ab7c5af | 78dc5fda4969acc9a34fe639ee7bc585bc8b90cd787ba350c60d8d377b33dee1 | NNP_L009/receipt.json |
| NNP_InstallField | bac42e20a47fb67e2c3cd81dd08326373649840740074cafd1e3ed1e70089eab | 81fbf6efba2c5db10b97c85698970a4a7b1e052d9ebbe4b627b033307076cde3 | NNP_L010/receipt.json |
| NNP_COMBINED_IMPORT | 68016161685f517cc1d2b7b577c44789e59258f57d091db3a8d432adcefd5dc8 | 278596c29586eb50420e50d3c60b60288d3d37f4d7bbefc9da6ec8f9df065ac1 | NNP_L011/receipt.json |
| NNP_Scan | 58b9fafd52ead6a7118c760e7db7fc91f1cf691d0b4784ad08ed588fa608d9b7 | 4aab8ad1f639312375494f0dd2e2774d47c49b89d064d388678093d41ce78d2b | NNP_L014/receipt.json |

## Validation, exports and boundaries

NNP_L011 combined import includes LIBB_GATE_IMPORT, unchanged LIBW and all six
NNP proof modules; exit0. NNP_L016 native NFX-style scan:17897 modules,
862956 declarations,zero dangling references and zero incompatible duplicate
owners. Same-shape cached replicas are reported separately. NNP_L016 then
raw-audits19 LIBW roots and25 new roots, all matching collectAxioms. Outer scope
exit0,129.5546888371464s,8056224KiB peakRSS,swap0; per-step timings are retained.

Budget16/16 scopes,one at a time;12 passed and4 failed. L002/L004/L005 are
elaboration failures; the twice-failed state-valued counterexample is retired.
L013 interpreted scan hit its memory threshold; L014/L015 replace that shape
with native code generation and optimized linking, then L016 passes the same
scan. No cap/timeout increase or unchanged failed rerun. Every launch has
count<6,free disk>=40GB,admission exit0 AND allowed:true,6G/8G/swap0/tasks64;
Lean uses-M7000 and async=false.0 Kani,0 extraction. No shipped source,RSL or
trust edit,no ELF rebuild trigger,no sibling worktree/cache mutation,no push.

Prepend export directory:
/home/dombarker/project-offloads/codex-cx-libw-host-20261108/NNP_exports_20261108

Then retain the LIBB_L344 LEAN_PATH. The export includes selected supplemental
NNH objects and private LIBB copies (123 object/sidecar files), with provenance
and hashes in NNP_EXPORT.json,NNP_IMPORTED_HASHES.json and compressed full
NNP_CLOSURE_PINS.json.xz. Selected Aeneas library objects are pinned. Own scratch
copies and native binaries were removed; export and receipts remain. No shared
cache was deleted. The coherent SInt2 closure is reused,not fully rebuilt.

Inherited release pins (not newly rebuilt):default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.
Headline remains AspisR1.RPx_Deployed.deployed,frozen3,L154 parameter,narrowed
D188,100-bit PER-ATTEMPT,privacy and two transactions. Full deployed source/runtime
composition and soundness are not established by this registration handoff.

Status details and remaining boundaries:../libw-host-20261108/NNP_REMAINING.md.

target not yet established
