# RSL canonical RowSpec package: index

Target not yet established. These are specifications, not proofs. No row is closed by this package.

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, release features {pool-adapter, private-leaf-salts}, with cu-profiling, prover and detail-phases off. Each module defines `RowSpec_<row>` over the observed semantics of the actual frozen function, `impl : Args -> [SdkState ->] Env -> Obs Ret`. The spec says that on the row's own-input domain, the observation lies in `Ref`, a line-by-line transcription of the frozen body. Read the header of RSL_Base.lean first. The semantic choices that make the package full-strength are these:

- **Complete Result.** Every `Ok` and `Err` value is exact. `ProgramError` is the complete solana-program-error 2.2.2 carrier, payload variants included.
- **Ordered effects.** Every observable effect is an `Event` in source order: the PDA, sha256 and Clock syscalls with their quantified replies (ruling (at)), log lines, return data, account-data writes and RefCell acquire/release tokens.
- **Aborts.** A panic, a stopped child or an allocation failure is `Exit.abort` with only the event prefix (ruling (bl)(3)). No post-abort state is stated.
- **Only one source of nondeterminism.** The only nondeterministic branch is the allocation-failure arm at each named allocation site. There is no generic "may abort" clause, so a constant Err or a constant abort cannot satisfy a spec. Each module proves this in Lean (see RSL_CHECK.md).
- **Child calls at SAME arguments.** A child is entered through `Spec.call dom law` (or `Child.run`) at SAME arguments. The parent spec is therefore provable only if the parent discharges the child's (bf)(2) domain at that call. Caller-clause discharge is part of the statement and is never a hypothesis.
- **The three NMG_ defects are avoided.**
  - The spec constrains the actual function's observation, not an invocation relation, so the empty relation does not satisfy it (NLJ094).
  - Every Returned or abort arm has its exact prefix (NLV).
  - The Box owners of TX2:233 are fields of the returned value, each with its allocation site. Their drops write no account or return data and are outside the obligation under (bl)(3), so nothing is erased (NLM 233/242).

## Interface parameters (instantiate exactly as named; the gate checks each clause)

`PoolLib` and `DeployedIds` are defined in RSL_Pool. `VLib`, `PreparedNew` and `Child` are in RSL_Verifier. `V2Lib` is in RSL_TX2_241 and `S1Lib` in RSL_TX1_345. `Stage1` is in RSL_TX2_221. None of them is a free Ops dictionary. Each field's comment names the single CLOSED root that instantiates it, and the field must be instantiated with that root's model at SAME arguments.

The rule for domains: a CLOSED child's (bf)(2) domain goes into `Child.dom`, verbatim from that child's ledger clauses. RSL_LEDGER_CLAUSES.json extracts these per parent row. For a Spec-valued PoolLib field, the domain is conjoined into the law instead.

Two consequences:
- Weakening `dom` or `law` relative to the CLOSED statement is a gate finding.
- A domain field instantiated as `False` cannot be discharged by the entry or headline caller, so it fails at composition.

Small CLOSED helpers are transcribed concretely in RSL_Base and RSL_Pool, for example the require_* checks, the snapshot, is_active_at, decode_digest_canonical and decode_*_box. For each of these, the worker proves that the CLOSED root implies the transcription on the call domain ((bm)(2)(c)).

## Rows

Shape key:
- **(bm)**: emitted Aeneas body under ruling (bm). Prove `RowSpec` for the emitted body with child calls interpreted by CLOSED roots, and with OPEN children as the RowSpec parameter already inside `Ref`.
- **(bj)/(bl)**: ReviewedTranscription of the guard-holding wrapper over the RSL SDK model, which transcribes NLF_RefCell/SdkModel/ParentModel. Add one native harness per branch with the owned child havocked over its full Result, plus a Lean fold equal to `Ref`.

### TX2:217 decode_lane_from_pool_release
| Field | Value |
|---|---|
| Frozen signature | `fn decode_lane_from_pool_release(bytes: &[u8]) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError>` |
| Spec | `RSL.TX2_217.RowSpec_217`, module RSL_TX2_217.lean |
| Own-input clauses | none |
| Children | decode_digest_canonical (CLOSED TX2:146, transcribed); V7_PAIR_EMPTY_ROOTS (literal table) |
| Shape | (bm) |

### TX2:234 authenticate_invariant_release_registry (owned version, which shadows r1_pool_adapter.rs:523)
| Field | Value |
|---|---|
| Frozen signature | `fn authenticate_invariant_release_registry(verifier_program: &Pubkey, pool_program: &Pubkey, master_account: &OwnedAccount, master: &PoolV1PairForestMasterV1, registry_account: &OwnedAccount, entry_account: &OwnedAccount, current_slot: u64) -> ProgramResult` |
| Spec | `RowSpec_234 L D`, module RSL_TX2_234.lean |
| Own-input clauses | none |
| Children | CLOSED TX2:220/225 (`D`); TX2:151 (`validatePolicy`); TX2:236/229/231 (transcribed); TX2:201-204 (decoders); TX2:194/196/197-200 (transcribed); PDA syscall slot |
| Shape | (bm) |

### TX2:233 authenticate_asq8_accounts
| Field | Value |
|---|---|
| Frozen signature | `fn authenticate_asq8_accounts(verifier_program: &Pubkey, accounts: &[OwnedAccount], pool_program: &Pubkey, output_lane: u8, current_slot: u64) -> Result<AuthenticatedAsq8Accounts, ProgramError>` |
| Spec | `RowSpec_233 L D`, module RSL_TX2_233.lean |
| Own-input clauses | none |
| Children | OPEN `TX2_234.Ref` and `TX2_217.Ref`; CLOSED TX2:235-238, TX2:229/231, TX2:216/218 (box bodies transcribed) |
| Shape | (bm) |

The ledger edges to TX2:016 and TX2:039 (`to_le_bytes`) are spurious: line 293 calls `u64::to_le_bytes`.

### TX2:242 validate_asq8 (owned)
| Field | Value |
|---|---|
| Frozen signature | `fn validate_asq8(verifier_program: &Pubkey, accounts: &[OwnedAccount], instruction_data: &[u8], current_slot: Result<u64, ProgramError>) -> Result<ValidatedAsqa, ProgramError>` |
| Spec | `RowSpec_242 L D`, module RSL_TX2_242.lean |
| Own-input clauses | none |
| Children | OPEN `TX2_233.Ref`; CLOSED TX2:163/158/156/220/229/226/224 |
| Shape | (bm) |

### TX2:241 stage2_owned
| Field | Value |
|---|---|
| Frozen signature | `fn stage2_owned(program_id: &Pubkey, accounts: &[OwnedAccount], data: &[u8], current_slot: Result<u64, ProgramError>) -> ProgramResult` |
| Spec | `RowSpec_241 L D V2`, module RSL_TX2_241.lean |
| Children | OPEN `TX2_242.Ref`; TX2:064 through `V2.tx2auth` with `Dom064` = NMN_064.Domain (proof 57607, checkpoint 1768, public ≤ 1880, Root0), instantiated with NMN_064.RowSpec's Law and chronology once 064 is gated; CLOSED TX2:229/165/211/212/219 |
| Shape | (bm) |

Own-input clauses:
- **(D1)** Every OwnedAccount is snapshot-consistent.
- **(D2)** Root0(accounts[6] bytes, accounts[0] bytes[688..58295]) whenever the proof image has 58295 bytes.

### TX2:240 stage2
| Field | Value |
|---|---|
| Frozen signature | `pub(super) fn stage2(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult` |
| Spec | `RowSpec_240 L D V2`, module RSL_TX2_240.lean, over `SdkState` |
| Own-input clauses | **(D2')** Root0 on the entry-state payloads of accounts[6] and accounts[0] (1768 and 58295 bytes) |
| Children | CLOSED snapshot TX2:239 (transcribed over the SDK model) ×7; OPEN `TX2_241.Ref`; Clock and return-data syscall slots |
| Shape | (bj)/(bl) |

The ledger edge to FibreIndex::get (TX2:043) is spurious: line 479 is `Clock::get`.

### TX2:221 process; TX1:333 process (same function, frozen body sha 326a0777…)
| Field | Value |
|---|---|
| Frozen signature | `pub(super) fn process(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult` |
| Specs | `RowSpec_221 L D V2 S1` (RSL_TX2_221.lean); `RowSpec_333 L D V2 V P C := RowSpec_221 … (TX1_344.asStage1 V P C)` (RSL_TX1_333.lean); `RowSpec_221_full` is the identical Prop |
| Children | OPEN TX1:344 (`S1`) and TX2:240 |
| Shape | (bj)/(bl) |

Own-input clauses:
- **(P1)** `pool_route::admitted(data)`. This excludes the lifecycle arms.
- **(P2)** (D2') on the ASQ8 route.
- **(P3)** The TX1:344 domain on the stage1 route (True).

Both rows carry the whole function's obligation (both routes). They close together by one root.

### TX2:213 process_r1_cost_probe_instruction; TX1:330 (same function, sha a8986009…)
| Field | Value |
|---|---|
| Frozen signature | `pub fn process_r1_cost_probe_instruction(program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult` (pool-adapter body only) |
| Specs | `RowSpec_213` (RSL_TX2_213.lean); `RowSpec_330 := RowSpec_213 … (TX1_344.asStage1 …)` (RSL_TX1_330.lean) |
| Children | CLOSED TX2:214 (transcribed `admitted`); OPEN process |
| Shape | (bj)/(bl) |

Own-input clauses:
- **(E1)** (D2') on the ASQ8 route.
- **(E2)** True on the stage1 route.

`data` is not restricted: non-admitted data must return Err(InvalidInstructionData) with no event and an unchanged state.

### TX1:136 verify_finish
| Field | Value |
|---|---|
| Frozen signature | `fn verify_finish<H: Digest32>(public: Public<'_>, prefix: Prefix<'_>, transcript: SemanticTranscript<H>, challenges: Challenges, obs: Observer) -> Result<Verified<H>, Error>`, with H = SolanaDigest |
| Spec | `RowSpec_136 V`, module RSL_TX1_136.lean |
| Own-input clauses | `V.finishInputDom public prefix transcript challenges` (see below) |
| Children | CLOSED TX1:134/130/129/256/076/141/147/024/029/146/142/139 as `VLib` Child packets |
| Shape | (bm) |

`V.finishInputDom` is the set of clauses that 136's children place on 136's own arguments and that 136 cannot discharge internally. These come from the ledger NJW/NKN/NLS records in RSL_LEDGER_CLAUSES.json. `obs` is unconstrained because mark is a no-op without detail-phases.

### TX1:137 verify_observed
| Field | Value |
|---|---|
| Frozen signature | `pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H, obs: Observer) -> Result<Verified<H>, Error>` |
| Spec | `RowSpec_137 V`, module RSL_TX1_137.lean |
| Own-input clauses | `V.publicDom public ∧ V.semanticBytesDom bytes` |
| Children | CLOSED TX1:138/130/131/150; OPEN `TX1_136.Ref` |
| Shape | (bm) |

`finishInputDom` must be derived from the parse, public_transcript and begin laws.

### TX1:087 prepare
| Field | Value |
|---|---|
| Frozen signature | `fn prepare<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer, g: &mut [E; 29]) -> Result<Box<Prepared>, Error>` |
| Spec | `RowSpec_087 V P`, module RSL_TX1_087.lean. The result pairs the Result with the final `g` on every returning arm |
| Children | CLOSED TX1:064/098/099/095/191/179 (`P`); OPEN `TX1_137.Ref` |
| Shape | (bm) |

Own-input clauses:
- **(R1)** proof.len() = 57607.
- **(R2)** obs = None (ruling (al)).
- **(R3)** `V.publicDom public`.

### TX1:094 tx1
| Field | Value |
|---|---|
| Frozen signature | `pub fn tx1<H: Digest32>(public: Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize, hash: H, obs: Observer) -> Result<Vec<u8>, Error>` |
| Spec | `RowSpec_094 V P`, module RSL_TX1_094.lean |
| Children | CLOSED TX1:086/084/191/174/081/181/176/088/175/186; OPEN `TX1_087.Ref` |
| Shape | (bm) |

Own-input clauses:
- **(T1)** obs = None.
- **(T2)** `V.publicDom public`.

### TX1:328 first_decoded
| Field | Value |
|---|---|
| Frozen signature | `fn first_decoded(public: …::r0::Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize) -> Result<Vec<u8>, ProgramError>` |
| Spec | `RowSpec_328 V P`, module RSL_TX1_328.lean |
| Own-input clauses | `V.publicDom public` |
| Children | OPEN `TX1_094.Ref` with obs = observer() = None; CLOSED TX1:NGB001 error (log line then InvalidInstructionData) and TX1:329 |
| Shape | (bm) |

### TX1:345 stage1_owned
| Field | Value |
|---|---|
| Frozen signature | `fn stage1_owned(program_id: &Pubkey, accounts: &[OwnedAccount], data: &[u8]) -> Result<Vec<u8>, ProgramError>` |
| Spec | `RowSpec_345 V P C`, module RSL_TX1_345.lean |
| Own-input clauses | none |
| Children | CLOSED TX1:339/340/341/335/342/332/276/267/278/173/268 (`C`, transcribed helpers); OPEN `TX1_328.Ref` |
| Shape | (bm) |

### TX1:344 stage1
| Field | Value |
|---|---|
| Frozen signature | `pub(super) fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult` |
| Spec | `RowSpec_344 V P C`, module RSL_TX1_344.lean, over `SdkState`. `asStage1` is the packet consumed by 221/333/213/330 |
| Own-input clauses | none |
| Children | CLOSED snapshot TX1:343 ×3; OPEN `TX1_345.Ref`; SDK try_borrow_mut_data (NLF law); copy_from_slice (std, panics on unequal length) |
| Shape | (bj)/(bl) |

## Clauses that are ambiguous, propagate to the headline, or may need a missing child lemma

1. **Root0 at the entry.** The Root0 provenance clause (D2)/(D2')/(P2)/(E1) is not checked anywhere in the program. It propagates from TX2:064's own domain (NMN_064.Domain.root0) through 241, 240, 221 and 213 to the entry state. There it can be discharged only by the headline hypotheses: RuntimePersistence data-only plus NMF_GameRoot "Root0 or the existing charged collision". At the entry row this is a (bf)(2) clause with no program caller. It is not vacuous: the honest TX1 write establishes it. But it must be listed against the headline inventory under (aq)(2) and (bf)(3).
2. **TX1:136's own-input clause set (`finishInputDom`) was not transcribed verbatim.** The ledger gives it as prose and foreign Lean (NJW/NKN/NLS records). It enters as a named `VLib` field. Its faithfulness depends on instantiating it with exactly the clauses that 136 cannot discharge internally. The same applies to `publicDom` (NLS-bf:TX1:136:TX1:256:hd) and `semanticBytesDom` (TX1:138).
3. **TX1:345 may need a missing CLOSED-child lemma.** It must derive `publicDom (semantic_public statement)` from the CLOSED decode and validate laws (TX1:332/276). If those laws do not export it, a child lemma is missing under (aq)(3). It is not a new domain.
4. **TX1:094 may need more from TX1:179.** It must discharge batch_merkle's clauses (NLO-bf:TX1:094:TX1:081 len, wire, canonical, rootValues) from parse_shape's law and from prepare's law, that is Prepared::new TX1:179. NMG_ reports that the TX1:179 caller domain is still open. If TX1:179's law does not export the root bindings, the gap is in that child's law (aq)(3), not in this spec.
5. **Spurious ledger inventory edges.** TX2:233 has edges to TX2:016/039, and TX2:240 has an edge to TX2:043. Neither is a call in the frozen body.

No ledger obligation was found to be vacuous or unsatisfiable as stated.
