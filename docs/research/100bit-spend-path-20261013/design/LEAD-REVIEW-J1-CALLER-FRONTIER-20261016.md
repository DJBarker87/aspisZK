# Lead review: caller-frontier checkpoint 5e841c471 (2026-10-16)

Merged as a merge commit, not a fast-forward: the branch had gained eight
live-session commits after 19c68d240 (fa0af9a18..31bd85417). The two sides
touch disjoint paths, all under this research directory; the merge was clean.
No production crate, program, or existing protocol-core module changed.

## What was checked

- Both evidence verifiers pass from the integration worktree:
  `decoder-public-bridge-20261016/verify.py` (192 members, 41 standard-only
  adapted reports) and `digest-interface-candidate-20261016/verify.py`
  (candidate-only inverses, rejected empty emission retained, three Lean
  targets, two standard audits).
- `ExtractedDecoderPublicBridge.decoder_serializer_parsePublic` was read
  against `CallerPublic.encoder_serializer_parsePublic`: it supplies `he`
  from `hd` (actual Withdrawal decoding success) and passes `hs` through.
  The transition `t` is a free argument, not bound to the decoded
  `c.lane_transition`; the report states this as open and it is.
- No `sorry` or `axiom` in the new Lean files.
- Compiles were not rerun by the lead; acceptance rests on the retained
  receipts and the verifier checks above.

## Accepted

- Worker C: the actual decoder → encoder → live parsePublic bridge for the
  Withdrawal variant. Withdrawal-only; privateTransfer is not covered.
- Worker A: the 33-row/state-carry inventory and the Digest32 candidate as
  feasibility evidence only. It is not a source change.
- Worker B: the SDK extraction diagnostic (Charon ok, Aeneas fails on
  `NonNull` in TypesAnalysis.ml:486) as a recorded negative result.

## Decision 1: Digest32 source migration (adopted), no extractor fork

`HashFn = fn(&[&[u8]]) -> [u8; 32]` in `aspis-core/src/transcript.rs` is a
function pointer with two bound regions that pinned Aeneas rejects. We
migrate the R1 verifier path to the `Digest32` trait (`fn digest(&self,
parts: &[&[u8]]) -> [u8; 32]`), as in the candidate, instead of maintaining
callback lowering in a forked extraction toolchain. A forked extractor would
put an unreviewed compiler change inside the trust base; the source change is
small and monomorphizes to direct calls.

Adoption gates, all required before the migrated source is the release source:

1. Exactly one production `Digest32` impl on the verifier path, delegating to
   the same syscall as today. The R16 syscall premise is unchanged in wording.
2. Byte-identical full traces on the existing 1,233-case terminal source
   differential, before versus after.
3. The saved-proof hash-counter regression passes with identical counts.
4. CU replay on the admitted fixture: no increase is the expectation. Any
   increase is recorded and reported to the lead before adoption.
5. The rebuild is folded into the single J1.R13 guarded SBF rebuild and artifact
   pin. There is no separate release rebuild for this change.
6. Re-extraction covers only the migrated modules, and all prior extracted
   theorems are re-pinned. A theorem whose statement changes is listed
   explicitly.

The live session's modules are not edited by the workers. Any instance
adaptation goes in worker-side bridge files.

## Decision 2: metadata helper (adopted), not full SDK semantics

`require_readonly_account` only reads `owner`, `is_signer`, `is_writable` and
`executable`. Aeneas's failure is in raw-pointer types (`NonNull`) inside the
SDK's `AccountInfo`, which it does not model. We will not try to model SDK
memory. Split the guard into:

- a pure helper, `readonly_meta_ok(owner: &Pubkey, expected: &Pubkey,
  is_signer: bool, is_writable: bool, executable: bool) -> ProgramResult`,
  extracted and proved: it succeeds iff owner equality holds and all three
  flags are false;
- a one-line wrapper that projects those four `AccountInfo` fields and calls
  the helper. It is kept in source and pinned by hash.

The field projection joins the R16 runtime boundary as one named premise:
the SDK's `AccountInfo` fields equal the loader-serialized account metadata.
This premise does not establish custody. It is backed by an adversarial
runtime test that rejects signer, writable, executable and wrong-owner
accounts, each separately. Both copies (`aspis-verifier` and
`r1-cost-probe`) get the same split. The source change rides the same gates
and the same J1.R13 rebuild as Decision 1.

## Still open (unchanged by this checkpoint)

hs from the actual caller; binding `t` to the decoded lane transition;
supplied-public equality; caller reachability and custody; privateTransfer
decoding; selected hread with actual records/challenges, htyped/ha and C2
provenance; J5/J2, J1.c/d, source-derived J1.e and verifier QV; efficient
extraction. None of these is claimed closed.
