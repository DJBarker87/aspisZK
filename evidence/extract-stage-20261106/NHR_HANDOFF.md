# NHR extraction stager handoff

IN PROGRESS. No deployed row or security target established. Frozen source:
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Only NHR evidence is writable.

Stage 1: discover all frozen workspace members and transitive manifest path
dependencies; stage and byte-validate them, then validate Cargo's offline locked
graph. Stage 2: extract prepare, tx1, tx2_authenticated and tx2_common separately,
checking opacity against LLBC. Stage 3: compile usable emissions with
NGK_COMBINED_IMPORT, standard axioms only, and publish pins/commands.

Budget: zero Kani; at most 20 compiler slots and 8 extraction attempts, one
admitted capped scope at a time. No theorem is requested. Failure and remaining
obligations will be recorded without native-credit claims. No shipped source,
wallet/key, sibling worktree or shared launcher is changed.

Prepare extraction: NHR_E002 PASS,63.035177s,539840KiB RSS,swap0. Raw output is
NHR_emitted/prepare_v2/raw/NHR_prepare; exact command, tool/source/lock hashes
and checked opacity spans are in its NHR_PINS.json. E001 is retained as an OWN
collector/input failure, not a tool limit. No Aeneas failure occurred there.
