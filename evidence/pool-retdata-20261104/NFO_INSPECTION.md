# Pool return-data inspection — stage 1

Status: source/ELF inspection only; no native certificate or headline claim.
Frozen source revision: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Both dispatch files are byte-identical to that revision.

## Path discrepancy

The job/ruling(ab) cites verifier_dispatch.rs:145,309,380. This is the
legacy ASVS 384-byte authenticator, not the ASR8 792-byte result emitted by
NFD's CLOSED emit_result. Its sole proof account CPI cannot be identified
with the eight-lane split-checkpoint CPI. No format equivalence is asserted.
The real ASR8 consumer is pair_forest_dispatch.rs:364–381. This is a
slice-boundary/path-inventory finding; native evidence must identify its own
path rather than give legacy evidence credit for the ASR8 join.

## Pinned ELF

NFO_INSPECTION_PINS.json records the exact Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
and both verifier pins (default f8c0ec72…, devnet 63ad3e9c…). All three were
hashed on the host, not rebuilt. Pool command selects
r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit.
The disassembly is stored once compressed, with its uncompressed hash.

At 0x3e78 the Pool calls the set-return wrapper 0x5fc98 with r2=0 (clear).
At 0x3eb0 it calls invoke wrapper 0x5f910. Its returning success tag is tested
at 0x3ed0; 0x3ed8 and 0x3ee0 prepare the output pointer, and 0x3ee8 calls
get-return wrapper 0x5fca8. There are no other calls between those two calls
on the read path. The wrappers tail-call 0x61018 (set) and 0x61028 (get).
The invoke chain reaches sol_invoke_signed_rust relocation 0x60f58;
set/get relocations are 0x61018/0x610a0. SDK return cleanup and get-buffer
initialization are not literally adjacent instructions; their effects must
also be inspected before a no-clearing-syscall claim is complete.

After readback, absence is tested at 0x3f08. Four 64-bit words of the returned
program id are compared at 0x4000/0x4018/0x4030/0x4050; mismatch branches to
InvalidVerifierReturnProgram (0x4153202c at 0x4060). Length must equal 0x318
(792) at 0x4078; mismatch selects InvalidVerifierReturnData (0x4153202d).
The decoder call at 0x40a0 receives the SAME data pointer r7 and length792.
Decode errors map to InvalidVerifierReturnData; success constructs the typed
Box and retains the exact returned bytes. These are instruction observations,
not yet a checked complete source/ELF refinement.

Source rejection order: pre-CPI account/program/checkpoint/registry shape
checks; CPI Err propagation with no read; missing data; wrong program; wrong
length; decode error; successful same result/bytes allocation. Legacy source
adds decoded expected-result and full expected-byte equality checks.
RuntimeReturnData is retained as ACCEPTED added trust; no runtime law is
claimed discharged. Wallets, keys, shipped source and release artifacts unchanged.

## Completed SDK success-path check

NFO_ELF_FLOW.json conservatively explores all branches and direct callees
from0x60f60 after sol_invoke_signed_rust, taking its r0=0 success branch,
through SDK return cleanup (18 instructions; only deallocation calls), and
from get-wrapper0x61028 through its read syscall0x610a0 (21 instructions;
only sol_memset_ initializes the output buffer). Zero unresolved/indirect
calls and zero intervening CPI/set syscalls in these intervals. Two planted
clearing/CPI relocation mutations are detected. Error-conversion paths are
excluded from this returning-success statement, since the caller propagates
CPI Err without reading. An initial over-approximation included formatting
indirect calls on error paths; narrowing to the actual syscall-success branch
removes those irrelevant paths rather than inventing their targets.
