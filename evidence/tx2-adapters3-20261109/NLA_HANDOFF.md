# NLA handoff — stage 1

Target not yet established. TX2:217 and TX2:234 remain OPEN; no ledger credit.
Branch codex/cx-tx2-adapters3-20261107; commits local, no push.
Baseline: ledger20 NKW_LEDGER, 560 CLOSED / 0 QUALIFIED / 39 OPEN.

Owned rows only: decode_lane_from_pool_release and authenticate_invariant_release_registry.
First reuse NKP final export, then NKW export, privately; no shared cache writes.
Native budget 70; formal/support budget 80; extraction budget 0; none consumed yet.
One scope at a time, 6G high / 8G max / swap 0 / 64 tasks, Lean -M7000.
Admission requires exit 0 and allowed:true; pre-scope free disk >=40 GB; own writes <25 GB.

Frozen verifier crates/program and lock: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Pool source: b936275465; Pool ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.
Verifier ELF pins inherited, not rebuilt or verified here: f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 and 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299.
No shipped files changed; no rebuild trigger. No keys/wallets touched.

217: missing root digest exact byte/Result/prefix cut and complete source/op50 assembly; retain loop frame, induction and allocation obligations.
234: missing ordered policy/readonly/data/decoder/PDA/address chains for both versions; PDA value remains quantified op38.
No new trust, Ops/root endpoint/success/history premise or security metric change is authorized.
Next: pin seeds, inspect actual stage interfaces, then controlled native cuts and smallest Lean modules.
