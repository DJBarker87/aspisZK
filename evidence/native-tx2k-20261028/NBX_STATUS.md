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

Own validation improvement after L003: NBX_build.py now resolves and hashes
all direct imported objects in actual LEAN_PATH precedence before each compile,
recording the map and SHA256 fingerprint in the input and receipt. This is a
stricter own validation script, not a change to any host launcher or admission.
The coherent IDa_Deployed.lean source matches repository SHA256
3fc1393814d827408cfd33215ab0e9140316572044c7d22c034e1f7774fe786e;
its object hash is7577d93fb255655da193b25ffc3cbd9b0bcf95c6e17cf0b218693de27533a46e.
No shared/coherent object or source is rewritten.

L005/L006 rejected before elaboration because the imported aggregate roots
refer to absent unchanged objects (PAln_Public, then RawTx1DigestLog). No new
field-selection theorem is accepted from them. The focused dependency builder
copies no source into a shared workspace: it compiles only missing unchanged
modules to the lane’s private retained cache, one capped scope each, recording
source hashes/direct import pins. No proved source is repaired or re-proved.
The FIq source-closure inventory lists47 missing objects; object dependency
loading decides which are actually needed. Source-only inventory is not a
claim that the coherent installed root has been replayed.

L073 rejected at the aggregate remaining-slot conjunction’s default200k
heartbeat limit; L075 showed the same normalization issue for op23 with an
opaque seed. No heartbeat/depth/memory/timeout increase. The seven-field
selection itself was isolated and accepted in L074. Single-field retention
modules now expose the seed record structurally (`cases seed`) before rfl;
this is a changed symbolic proof shape, not an unchanged timeout rerun.

L076 also rejected at default200k after the first structural split. L077/L078
instead establish a symbolic closed form of the configuration’s adapter and
abstract SDK request/emission retention; registry/account SDK retention reuses
NBK’s existing theorems. Per-slot proofs now rewrite these named lemmas before
reducing the tiny final record update. This permanently removes the failing
large SDK/configuration normalization shape. No limits are raised.
