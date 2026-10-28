# Named world signature and identity obligation

PV_RunJoin_OsWorld is an explicit candidate world, not an installed native
interpretation or a proof of its laws. `Laws` consists of predicate DATA;
`EntropyAllowed`, `FileAllowed`, `TimeAllowed`, `WorkerAllowed` are obligations.
Exact Lean statements are printed by the focused target.

The shared entropy carrier is definitionally the existing
`PV_RunJoin_CallerWorld.RawTape E = Fin 128 → ((Fin 64 → Fin 256) × Option E)`.
`entropyUsed : Nat` retains the consumed position. A permitted draw at i requires
`world.entropyUsed = i.val ∧ world.entropy i = reply ∧ laws.entropyDraw world i.val reply`.
Neither uniform errors nor availability is asserted.

For dictionary alignment specialize `File := PDict_FileCarrier.File`,
`Reply := PDict_World244.Reply`. The request correspondence maps each of the
five constructors open64/read/write/sync/close to the identically named
PDict_World244 constructor, preserving every argument. Map each event by
that request correspondence and identity on reply. The exact identity
obligations for a runjoin world r and dictionary world d are:

- `d.entropy = r.entropy`
- `d.entropyUsed = r.entropyUsed`
- `d.files = r.files.map (fun e => ⟨requestMap e.request, e.reply⟩)`
- `d.fileUsed = r.fileUsed`

`requestMap` must commute with fileStep/step; the actual dictionary must use
that same d before and after every call. This commuting identity is not proved
merely by preserving the entropy signature. No dictionary world is imported
or silently replaced from the other branch.

Exact effect predicates at the pre-call world r:

| Effect | Predicate |
|---|---|
| entropy | `entropyDraw r i reply` plus cursor/slot equality above |
| open | `open64 r path flags mode reply` |
| read | `read r owner count reply` |
| write | `write r owner bytes reply` |
| durability sync | `sync r owner reply` |
| close | `close r owner reply` |
| time | `timeStep r = some (t,next) ∧ laws.time r t` |
| worker scheduling | `workerStep r = some (w,next) ∧ laws.worker r w` |

Each file predicate also requires the exact `fileStep request r = some
(reply,next)` equation. Reply must retain outcome/error, resources, visible
bytes and side channels from the dictionary Reply. Its outcome predicates
are not theorems about native OS behavior. Unix File::flush has the pure
`flush r = r` equation and consumes no event; it must not be conflated with
sync_all durability. E1 constrains entropy conditional on the full public
frame, including these outcomes; E2 must identify reserve results and ledger
history with this SAME consumed filesystem history. Those matching laws
remain open.
