# SbfProducer source-only candidate

Entry: 338af425c97277de9bb3c9bd7d6f7c4841cc6f53. No actual host, privilege,
compiler, native, scope, probe, extraction, ELF or RPC operations are authorized.
All source inputs come from immutable Git blobs. This document precedes code.

## Source assessment

* SbfLinux 9f50be799e: concrete ABI/backend/capture, 54 historical mock cases
  reused, not rerun. CLI always denies. Runtime and producer assembly absent.
* RssGOv3 45d137dd34: copy collector, sealed loader, evaluator dependencies and
  sampled guard exactly with recorded identity substitutions. Preserve 55/7/2
  GiB policy and its full raw observations, including errors and reservations.
  Its historical 552960-byte denial and six prior failures are not new gates.
* SbfSeal b6ac47947b: projection and ancestry model are design references only;
  neither can authorize execution. Meta1G c7bbb is never a 4GiB authority.
* Runtime087 is not approved. RuntimeTrace58497 is not read. No runtime manifest
  or signature will be invented from partial acquisition or older evidence.

## Concrete intended flow

Fixed future user unit SbfProducer-20261025-tiny-v1.scope, 3G/4G/0/64.
Inside it, pin package/runtime/environment/inherited limits before and after
concrete full read-only admission. Additional reservation is zero; the own
finite cap is already included once in Q0. A resident user guard tracks the
actual collector, sudo, optional monitor, helper and descendants. Then only a
fixed no-argument sudo launcher can enter the parameterless root continuation.
Root reopens its own root-owned package, recomputes full admission using its
actual current scope identity, and reads actual bounded process ancestry.
No caller report, marker, GO callback, arbitrary argv, manifest or environment
is an authority. Source-only tests substitute individual read APIs explicitly.

Root source/runtime pins and fixed controls must survive the scan; all pending
metadata FDs close before backend setup. The concrete backend call is through
the control gate. Missing approved runtime prevents reaching native loading.
The installed public CLI remains unconditional denial even if metadata changes.
Activation remains a separate unapplied review patch, requiring a new reviewed
release package and separate deployment/probe allocation.

## Acceptance criteria and limits

Byte and AST identity must hold after reversing exact recorded renames for
unchanged copied modules. Changed functions have explicit before/after source
and delta assessment. Tests exercise real policy on synthetic raw snapshots,
fresh collection ordering, wrong unit/caps/source/environment/ancestry/start,
package aliases/writers and error paths; no native backend is executed.
One changed-source suite only, local Python below 512MiB, exact receipt pins.

Runtime closure must include Python startup before verification, stdlib and
extensions, ELF loader/libs, sudo and optional monitor, collector command tools,
their loaders/configuration and source import closure. Published trace review
must settle this; hashes are not a proof of effective loader isolation.
SIG0 does not prove LSM permits SIGKILL. D-state waits are unbounded. Parent
death after releasing the child gate and credential changes clearing PDEATHSIG
need explicit lifecycle handling or an OPEN execution gate. No tests discharge
kernel/native/project/loader trust or future physical memory availability.

No cleanup deletes keys or capture state. Root capture files stay retained on
failure; close owned descriptors and reap only owned children. No general
root reader, shell, environment override, numeric-PID kill or cap raising.
