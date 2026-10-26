# Physical-map, loader and root composition

Target not yet established. The requested CPS_Top.deployed with the original
quantifiers and only TwoTransactionLaw replacing L094--L096/L180 is NOT proved.
Do not identify CPS_SourceTop.correlated with that target.

CPS_BoundaryLoad.writer_positive derives positive writer funding from actual
native TX1 acceptance when its Entry is constructed by the local transaction-
boundary cache loader. No positivity hypothesis is present in that theorem.
This differs from Hist_RuntimeEntry.load, whose data projection does not clear
zero-funded accounts; connecting the original root Entry to the real boundary
loader remains a source/runtime interpretation obligation.

CPS_PhysicalKey.loaded/boundary preserve physical public-key metadata through
both load projections. pairing proves the exact global-map implication:
common injective physical map + two map views + equal writer/reader public keys
implies equal BANK cell labels. These three hypotheses are visible and are NOT
derived from the separate per-entry admission records. independent_maps isolates
why identical local cell labels cannot alone be used across transactions.

CPS_Ordinary.owner derives the owner guard on the SAME accepted native writer
Entry with the explicit pure op36 key-equality interpretation. Together with
CPS_EntryFlags.writer, the checkpoint is owner-checked and nonsigning.
CPS_Ordinary.of_flags exposes exactly the runtime fee-signature and nonce-owner
rules needed to turn those source facts into ordinary-key eligibility. Neither
rule is silently put into RuntimeEntrypointAdmission or adopted as trust.

CPS_SourceTop.correlated composes actual T2R_Top.deployed on the original entries,
inputs, Claims/bounds and SAME f,s,run,tx2 witnesses. Its history events are the
computed ordered CPS_BankRecorder source events. There is no physicalEvents
callback and no eventsView hypothesis in this theorem. This is source-model
progress only: initial bank/Entry interpretation, positive funding, op36 law,
complete source actions, consecutive ordinary physical pair, parent-final
image/status and TX2 loader view remain explicit. It does NOT identify the
computed source events with a deployed bank trace. Nor does it restrict the
original theorem's acceptance/caller continuations differently: only the
constructed history is passed to them; P2Prime/FirstEntry remain unchanged.
The old physical theorem remains available when physical event interpretation
is needed. Replacing its supplied physical event carrier by a computed source
event carrier must not be called deployed event discharge.

L009 (CPS_BoundaryLoad) failed parsing a pipeline projection and needed an
explicit rfl after rewriting the cache load. Corrected source passed L010.
L011 PhysicalKey, L012 Ordinary and L013 SourceTop all passed with standard
axioms only. Full AGENTS section6 fields, source snapshots and axiom lines are
in CPS_L009--013/receipt.json. All swaps0; same admitted caps and pinned cache.
No unchanged replay, timeout, memory kill, cap increase or Kani run. Budget
13/100 Lean, 0/10 Kani. Shipped files/artifacts unchanged; no rebuild trigger.

Next: audit fully elaborated before/after statements and test whether physical
pairing and parent success can follow from the original uncorrelated interface.
