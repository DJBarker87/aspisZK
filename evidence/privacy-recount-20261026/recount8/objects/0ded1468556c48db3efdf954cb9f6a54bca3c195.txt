# Stage 1: residual audit (in progress)

Entry revision 4148e0e59c. Original endpoint unchanged. Runtime/boundary 2→2;
original premise fields 8→8; partial constructor residual fields 6→6.
Exact six statements: residual-exact-statements.json (notation/binders in
PV_RunJoin_SourceEndpoint.lean). These are NOT six pure extraction facts.

| Field | Required evidence | Pure source? |
|---|---|---|
| E1_V329 | distribution of native entropy conditional on public frame | no |
| native_ledger_V337 | source IO projection into ledger history and reservation | no |
| byte_blind_V338 | public fault schedule, initial-ledger independence, causal frame | no |
| kernels_V339 | actual native weight equals product conditional kernel | no |
| disclosed_V038 | complete disclosed view, outside the unchanged bad event | no |
| observerOracle_V038 | complete oracle view, outside the unchanged bad event | no |

Both release fixtures inherit the existing pure source/body and provider-frame
proofs, but fixtures cannot discharge these universally quantified native laws.
The seven data inputs remain explicit. No owner adoption of option A or B.

The pure-source sub-obligation actually available to discharge is dictionary
map_err parametricity. The sibling selector has exact law
`@ExternalFuns.op12 b ops = @ProverRwOuterMapErr.map_err`
(PDict_MapErrTransport222.MapErrLaw). PV_RunJoin_MapErrInstalled uses that same
identity; its `selected` constructor proves it for ProverRwOuterMapErr.selected.
This does not assert that arbitrary externally supplied dictionaries select it.

World alignment read with git show, never edited: PDict_World244.World E is
PDict_EventWorld244.World (PV_RunJoin_CallerWorld.RawTape E) Request Reply.
Requests: open64(path,flags,mode), read(owner,count), write(owner,bytes),
sync(owner), close(owner). Reply includes outcome, resources, visible bytes,
sideChannels. PDict_FileWorld244.flush is pure no-op and consumes no OS event;
therefore a separate environmental flush-success assumption would be incorrect
for that Unix source leaf. Time and worker schedules need separate fields.

Quiet window honored through 18:15 UTC: no capped host scope before then.
New small local modules use only retained compiled caches and lake env lean.
Attempt IDs used locally are still globally unique within 25600–25899.

## Checked continuation result

PV_RunJoin_ContinuationProjection.after_reserve proves full proof/error status
and retained-header projection through the emitted post-reservation caller,
for arbitrary state carriers and projections, under MapErrParametric.
PV_RunJoin_MapErrInstalled.installed discharges that law under the sibling's
exact op12 identity. Attempt25609 exit0;34.5433s;3160014848bytes RSS;swap0;
standard axioms [propext, Classical.choice, Quot.sound]. This replaces the
failed23505 continuation proof. Attempts25602–25606 are changed-source
elaboration failures;25607 hit the default heartbeat limit. Replacement uses
separately checked bind/conditional congruence (25608, no axioms), no overrides.

Before: continuation/header projection unproved even with parametricity.
After: post-reservation continuation projection proved generally; full caller
projection and actual installed native dictionary remain next. Residual6→6,
endpoint8→8, runtime/boundary2→2. No quantifier/carrier/failure-event or observer
change to the original endpoint. No whole native row discharged.

## Full source/header projection checked

PV_RunJoin_LedgerSourceProjection.caller (25616) now projects the complete
emitted generic caller with the ledger-world callback to the actual
`prover.prove_masked_attempt`, retaining the full proof/error status and
source store header. The only dictionary hypothesis is the exact pure op12
identity used by dict10. PV_RunJoin_LedgerSourceBody.source_law (25618)
installs that projection as BodySourceLaw for the existing LedgerBody and
proves its provider frame. Intermediate reservation, guards, body and caller
projections are separately checked (25612,25613,25614,25615).

Before: only reservation callback source/header projection; complete body
projection open. After: full source/header projection generally checked.
No fixture-specific native dictionary or actual source-input family is
fabricated. No OS/world association inferred from the header projection.
Original six native residuals remain6→6; endpoint8→8;runtime/boundary2→2.
This permits constructing a ledger-world interpreter with a proved source
field; it is not yet the actual proof-account Runtime/Boundary instance.

## Named effect world checked

PV_RunJoin_OsWorld (25620) prints the exact entropyDraw/open64/read/write/sync/
close/time/worker predicate fields and their Allowed statements. These are
predicate data, never axioms and never declared valid for a native world.
World matching obligations are in world-identity-obligation.md, with sibling
read pins in sibling-read-pins.json. Flush is the source Unix no-op; actual
durability uses sync and its fallible outcome. No extra availability premise
is adopted. The complete source source/header theorem does not erase these
native effect obligations.

## Exact printer and transfer

ResidualPrint25624 prints each of the original six field declarations at its
full elaborated type, and audits both unadopted A/B theorem constants against
the retained cache (standard axioms only). Original endpoint statements stay
unchanged. SourceTypes25623 prints the actual source store and reserve trait
body; the complete source store has only directory and last_error, confirming
why source-header equality alone cannot recover filesystem history.

The previously refused archive transfer was completed after18:15UTC using
fresh admission02 (allowed=true at18:16:15UTC, requested0bytes, reserved
26172456960bytes). Host and local SHA256 agree: cache-transfer-01.json and
cache-transfer-01-host.sha. Archive6062708bytes, kept only locally and in the
assigned host directory; no archive/object/binary committed. This retains
focused cache evidence and is not a frozen release replay. No host compile
was launched during or after the quiet window for this transfer.
