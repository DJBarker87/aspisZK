# Required OS facts, not assumptions installed by this job

The exact three T fields remain entropy_law, entropy_kernel, observation.
None specifies open/write/sync/close transition semantics. Observation can
transfer an already defined extracted observation, including failures; it
does not prove that its transition laws are true. Entropy fields grant no
filesystem guarantees. The adopted public-error option still requires a
witness-independent failure-event theorem.

| Fact | Required law and dependent claim | Disposition |
|---|---|---|
| exclusive creation | With the same pathname resolution/namespace and create_new flags, O_CREAT + O_EXCL atomically creates only if absent, and two contenders cannot both succeed; existing-file failure preserves the existing contents. Include symlink/path/permission/error behavior. | FINDING W-OS-1 for owner: not stated by existing T. Required for no duplicate successful reservation in one running namespace. No availability assumed. |
| write_all | Each partial write advances the owned descriptor/cursor and changes precisely the written prefix; Interrupted retries; zero progress yields WriteZero; errors retain prior writes. | P obligation V267, not an atomic-write or rollback assumption. |
| fsync(file) | Successful return has a specified durable-data/metadata consequence; errors may follow partial persistence. Define crash/recovery/storage model and device ordering. | FINDING W-OS-2 for owner: not stated by existing T. Needed for reservation bytes surviving crash. Ordinary return-value correctness alone does not prove this. |
| fsync(directory) | Successful sync of the relevant parent directory makes the created directory entry durable in the same crash model. Account for mount/filesystem support and error paths. | Part of W-OS-2. Needed with file sync to prevent nonce reservation loss and nonce reuse after recovery. |
| close/Drop | Exact ownership, descriptor release and behavior on errors/unwind. No retry-close rule without handling descriptor reuse. close is not a replacement for durability sync. | P obligation V271 and reached V170 cases. |
| entropy/failure | Draw cursor/order, partial-buffer/error behavior, no unsupported progress/availability promise. E1/joint-kernel laws apply only on their stated carriers. | P step law plus unchanged entropy trust fields; failure witness independence still open. |

W-OS-1/W-OS-2 are explicit owner findings requiring a primitive/source and
recovery-law disposition. T remains capped at its existing three fields; this
job proposes no added T field and assumes neither finding in a theorem.
The consequences are distinct: concurrent exclusive reservation is not crash
non-reuse; file durability without directory-entry durability is insufficient
for the latter. Exact source flags and error mapping remain P proofs too.
The Linux man-pages corroborate the distinction: [open(2)](https://man7.org/linux/man-pages/man2/open.2.html) documents O_CREAT/O_EXCL and its filesystem caveats; [fsync(2)](https://man7.org/linux/man-pages/man2/fsync.2.html) states that file sync does not ensure directory-entry durability. These documents guide the required specification; they are not machine-checked P proofs or adopted T fields.


D364 resume: the new OsFile tape interpreter consumes a matching request and
retains its complete reply, including native error payloads as values. Its
filesystem/process update is explicit interpreter DATA. Neither consuming a
`.sync` event nor returning a successful reply proves data persistence, durable
directory entries, O_EXCL atomicity, witness-independent failure, or a native
close/Drop law. The source-to-binary and complete D159 payload obligations
remain; no side-channel component is declared irrelevant.
