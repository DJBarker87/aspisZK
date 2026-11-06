# Reference scope and outstanding native interpretation

This is a candidate specification, not a certified SDK law. Account count is
3 or 7, account index < count, all reached account.cell < 7. Heap owns all
payloads; live non-copyable Guard tokens refer to allocated cells. For a shared
live token the same cell counter is positive; for an unsplit exclusive token
it is -1. Drop consumes that token, not an arbitrary bit pattern. Deref_mut
and copy additionally require an exclusive token. All account metadata,
non-selected cells and non-selected payload coordinates must be framed.

Public constructors are a specification convenience; callers must prove the
valid live-token invariant. Rust ownership of this reference does not itself
prove the native Ref/RefMut correspondence. No pointer is fabricated from
integer words. A proof about these references alone earns no SDK credit.

Clock errors cover every u64 status and every ProgramError::from branch,
including Custom(0), truncated custom codes and BorshIoError("Unknown").
PDA statuses >=3 abort in the actual PubkeyError conversion; they are retained
as Abort, not represented as an SDK returned error. Seed validation precedes
the runtime call; op38 supplies only its arbitrary reply, with no value law.

Native ABI obligations include ordered seed descriptors, same program id,
output allocation, reply/status association, exact frame, and all rejection
prefixes. RuntimeEntrypointAdmission supplies initial heap facts only.
