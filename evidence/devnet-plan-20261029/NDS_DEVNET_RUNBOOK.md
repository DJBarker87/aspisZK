# NDS devnet runbook — BLOCKED, not executable or approved

**STOP before deployment.** No ordered deployment/wiring command sequence can
satisfy the existing-Pool request with normal instructions. A successful local
rehearsal and lead command review are prerequisites, neither satisfied here.
This worker is prohibited from every public-cluster write, even though the
contract records the owner's conditional devnet approval.

The existing registry PDA FUHo4ZRK5Q8TGkaMvUZhwyjXmCGz8qSR6hG19XwTycBr is
frozen with zero authority. ScheduleProfile immediately rejects it; no unfreeze
exists. A new verifier cannot be substituted merely by changing client config.
See NDS_PROCEDURE.md for exact code, state and receipts.

Required resolution before a concrete write runbook:

1. Owner/lead decides whether to authorize a fresh mint/Pool state and registry
   under the unchanged Pool/registry program IDs. This preserves the release
   verifier's compiled deployment IDs but does not migrate existing notes.
   Otherwise bring an explicit source/protocol/redeployment proposal back to
   the owner, assessing invalidated gates per AGENTS.md §6. Do not patch the ELF.
2. Locate the retained payer securely; verify existence, 0600 permissions and
   public key only. Documented host paths are currently absent. Retain all keys.
3. Resolve funding: payer 3.708326 SOL; permanent deployment estimate ~7.9542 SOL
   including estimated fees; conservative transient reserve ~15.8988 SOL before
   refund/reuse. Recheck live balance and exact allocation/fee behavior during
   the authorized local rehearsal. Wiring and spend costs are additional.
4. Rehearse the chosen scope on a local validator with cloned devnet programs
   and relevant accounts; explicitly loopback-pin every signing/write endpoint.
   Preserve runtime/version/features and cgroup resource receipts. Use fresh
   retained local keys; do not modify cloned authority bytes to bypass the gate.
5. Produce and review every exact command, output expectation, verification,
   signer path, new program public ID, buffer identity and recovery path. The
   repository scripts/config cannot be executed unchanged: historical ELF pin,
   identities, genesis check, setup state and automatic spend must be addressed.
6. Only after successful local TX1+TX2 and lead review can a separate authorized
   writer execute the reviewed devnet sequence. No such sequence is supplied
   here, because it would conceal the unresolved wiring step.

Required final verification specification (future runbook must implement it):

- Read finalized executable Program account owned by loader-v3; decode tag 2
  and its linked ProgramData address. Read that ProgramData at finalized
  commitment, require loader owner/tag 3 and Option authority byte 12 = 0.
- Extract ELF starting at **offset 45**, including legitimate trailing zeros.
  With reviewed `--max-len 1563728`, require payload length 1,563,728 and SHA256
  **63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299**.
  If allocation differs, use NDQ's ELF extent check and require zero allocation
  suffix; never blindly strip trailing zero bytes.
- Verify the new registry entry pins that program, ProgramData and executable
  hash, is active, and belongs to the intended Pool/policy/profile/release.
  Recheck Pool policy and frozen registry state, then TX1+TX2 outcome/accounts.
- Retain finalized slots, signatures, account snapshots and refund evidence.
  Never delete a buffer or program key while it controls value or authority.

Repository immutability mechanism is deploy, byte-verify, then
`solana program set-upgrade-authority PROGRAM --final`; the paced script uses
this explicit separate command, not a deploy finalization flag. This description
is not authorization or a reviewed command sequence.
