# NBX stage ledger

Inherited branch text said date27; actual branch is
codex/cx-native-tx2k-20261028. No branch switch, merge or push.

Stage 1: scope/read-only inspection committed as 0fe259acb7.

Own input repairs (no launcher/infrastructure edits):
- K001 failed during compilation because inherited NBU_tmp was removed by
  prior cleanup. NBX_native.py now creates NBX_tmp and uses NBX_target.
- K002 failed Rust type-check due duplicate NBX_status name (constructor vs
  harness). Rename arbitrary constructor to NBX_any_status. No theorem credit.
- L001 rejected record update layout and unavailable Aeneas Result.map;
  repaired with one field per line and explicit ok/fail/div cases. No theorem
  with sorryAx is accepted; the failing receipt is retained.

Scopes are serial. Every Kani attempt has its own frozen graph check and
unchanged-lock postcheck. No compile/memory/timeout cap is increased.
Source inspection confirms op53 has a runtime return-data write. No purity or
full extraction claim is made from the inspection or candidate SDK update.
