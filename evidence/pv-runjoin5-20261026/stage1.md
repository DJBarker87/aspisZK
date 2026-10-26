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
