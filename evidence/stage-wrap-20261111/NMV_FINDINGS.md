# NMV findings and rejected shapes

- NMV-E1: Actual snapshot Charon succeeds, Aeneas fails during field projection of opaque AccountInfo: `Can't retrieve the variants of non-adt type ... solana_account_info::AccountInfo`. This confirmation is not a proof that transparent AccountInfo necessarily fails, nor a guard-drop diagnostic. Binding (bm)(1)/(2) independently retains (bj)/(bl) for these guard wrappers. One extraction used; no further extraction authorized.
- NMV-I1: L001 was an own argparse omission; no extractor launched. L003/L006 stopped in own direct-import pin preparation (missing NLF/NLM fallback paths), no scope/compiler launched. L004 rejected the snapshot equality proof before a `dsimp only` repair; failed `sorryAx` output is retained and NEVER accepted. L007 rejected deriving DecidableEq for the external PE; derivation removed. These are own input repairs, not host infrastructure faults.
- NMV-K1: K001 compiled until a missing frozen cfg(kani) path module tools/r1-builder-reference/tree.rs. Full frozen reference package copied and hash-pinned. K002 compiled but the command selector omitted the real namespace; corrected without renaming any source function. Neither is a semantic pass/control failure.
- NMV-K2: K003 rejects a free late-bound-lifetime SDK getter stub (method carries one early-bound impl lifetime); K004's type-generic alternative ICEs (`expected type ... but found Lifetime`). That type-generic shape is retired. The lawful signature repair binds the SDK impl lifetime early (`'info: 'info`), keeping the receiver loan late-bound; no fake type-generic substitute remains. No Ref/RefMut is fabricated or stub_verified.

Native small carriers are explicit bounded diagnostic/call-boundary classes until composed with the complete universal NLF/std laws. No small-buffer result is promoted to a whole release buffer result. No unreviewed RowSpec, global native equality, successful-child premise, or post-abort world may be installed at a row root.

- NMV-R1: The client started L012 admission while K006 was still completing. The L012 reservation receipt lists the active K006 scope; the two own scopes overlapped briefly, violating the one-scope rule. Both retained their fixed 6G/8G/swap0/tasks64 caps. No resource compliance claim covers that overlap. Own transport now additionally rejects/waits on any populated scope whose command names this job's workspace. Shared admission/launchers are unchanged. Exact host timestamps are retained in NMV_SCOPE_TIMES.json; neither run is silently discarded.

- NMV-I2: K011–K013 were compile rejections because a long-lived queue imported the runner before its new parent-source upload rule. No semantic verdict or control credit. New queues stop if VERIFICATION is absent or an unwinding assertion occurs; the parent file is now an explicit patch/source input.
- NMV-K3: K005 failed only builtin memcmp32 unwinding. K006 replaces whole key comparison with one arbitrary coordinate; unwind stays8. K006–K010/K014–K016 have real final verdicts, retained separately from compile diagnostics.

- NMV-K4: K017 whole-seven-account stage2 error timed out at the unchanged external90s limit (no final solver verdict). Wrapper RSS100044KiB is NOT aggregate CBMC RSS. This shape is retired, no native credit. Replacement: snapshot is cut at its already-checked small free/read-shared boundary (no seven SDK RefCell executions), and one fixed original account is observed per harness. No timeout or cap increase, no unchanged retry. Exact child Args and universal accepted-snapshot content/clock/clear transport remain separate obligations.

- NMV-K5: K018 fixed-account0 with a snapshot-law cut still timed out at90s. The unique-RefCell seven-account parent family is retired after two timeouts, with no further account-port runs. Unit stage1 proceeds independently. Its changed native constructor uses two real Rc/RefCell allocations shared among descriptor views, preserving arbitrary metadata and an independent checkpoint cell. That is a diagnostic alias class, not a new own-input premise or general native producer. No claim about all runtime alias partitions is made.

- NMV-K6: K020 full-ProgramError stage1 error and K021 stage1 return both timed out at90s. The RefCell-logging whole-parent family is retired. A distinct local-record diagnostic replaces only harness-owned logging RefCells with disjoint stack UnsafeCell records, and keeps the harness's original account array in ManuallyDrop under(bl)(3) (private Rc cleanup is not a row effect). Actual stage1 and its SDK/copy sites remain unchanged. This is not a caller restriction or a stronger domain clause; universal native producer credit is still absent. No record is static and no guard is fabricated.

- NMV-K7: K023 local-record return still timed out90s. Inspection of the test helper found both stage1 and stage2 syntactically present under a const-generic selector, while each harness cut only its selected owned child. A replacement direct stage1 helper removes the unrelated TX2 call from the native harness source and avoids constructing an unused full-error oracle on the success branch. This isolates the actual frozen stage1 call, not a copied parent body; original harness identity is retained. No verdict is attributed to the unselected cone, no timeout is increased, and the broad selector helper is retired.

## Resume review

- NMV-K8: The WIP also contains K025 (90.659s, exit124), a further stage1
  local-record return attempt after K023/K024. Its source hash differs
  (`NMV_parent.rs`6005bd94… versus6171ce7c… atK024), so it was not an unchanged
  rerun, but it remains a near-duplicate in the already failing return family.
  It supplies no native credit. This continuation retires the entire family
  and does not launch another parent-return specialization. The late WIP
  attempt is retained for lead cost-rule review rather than omitted.
- NMV-I3: The WIP had archived the harnesses into NMV_HARNESSES.patch but left
  NMV_program.py reading removed raw .rs files. The own runner now reconstructs
  only added cfg(kani) artifact files from the committed patch. No shared
  launcher/validation/source pin is weakened. New shared-loan harness generation
  uses immutable68730c8ae22 as its archived input and is deterministic.
- NMV-G2: The proved G2 is a complete SDK/account-state frame on RETURNS,
  including all borrow-token cell fields and exact token-counter progress.
  RSL carries no post-abort state. It is parametric in the full weak packet;
  neither an actual native packet nor arbitrary-dictionary event-write exclusion
  is claimed. NMV_REVIEWED_TRANSCRIPTIONS.json records the exact scope.

- NMV-I4: L079 own retention omitted its NMV_ENV.json input. It failed after
  hashing/export, before tool-pin/retention completion. L080 supplies that
  archived file and passes the same validation; no proof replay, timeout/cap
  change, shared infrastructure fix or final credit from L079.

- NMV-E2 (bn resume): E003/L081 Charon translated both generic, guard-free
  fission wrappers, Aeneas failed with internal `Not_found` in context-collapse
  joining (not guard Drop). E004/L082 isolates only stage2 and reproduces the
  internal context-join failure (0.781s/141504KiB/swap0). Neither emitted a body;
  the two-extraction allowance is spent. This generic-log extraction family is
  retired. Proceed to (bn)'s explicit-window Kani fallback, retaining the exact
  mechanically checked copies. No body or post-loop-return audit pass is claimed.

- NMV-K9: K045 combines two independent full ProgramError enum generators
  (Clock and child), symbolic child Vec extents and whole-argument coordinate
  checks. It times out at the unchanged90s external limit; no verdict/credit.
  This cross-product shape is retired. Split into full child reply with
  successful Clock, and full Clock reply with successful child. The source
  wrapper is unchanged; each independent reply/argument/footprint check is
  retained. No timeout/cap increase, no unchanged rerun. Reported parent/time
  RSS is only the timeout wrapper, never aggregate CBMC memory.

- NMV-K10: K046's strengthened whole-reply/whole-coordinate checker also
  times out90s. Retire the combined checker family after its two failures;
  do not run its remaining controls. Replacement is independent, disjoint
  slice-descriptor forwarding (pointer+length, immutable input), full Clock
  reply forwarding to an owned local slot, and checkpoint Vec descriptor
  forwarding. Original K035-K044 full-child enum/control evidence is retained.
  These cuts add the missing descriptor/Clock facts without another enum
  cross product or native payload scan. Every buffer-content law stays Lean.
