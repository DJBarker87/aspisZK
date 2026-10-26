# Shared host path loss

At approximately19:51UTC the shared launcher, source, and evidence paths ceased to exist. No repair, cache replacement, or host configuration change was attempted.

- Last actual compile24070: R1Z/PV_CB_Op105Funs, exit1,2.63s,2621968KiB,swap0. It failed on the emitted `wrapping_shr exp 1#i32` (backend expectsU32). Full receipt retrieval then failed because `.../aspis-fs-generic-20261006/evidence/out-24070.log` was absent. `24070.json` explicitly records the limited stdout evidence and reconstructed local source hash; it is not acceptance evidence.
- The local correction changes only that shift count's type to1#u32, preserving the numeric shift amount. It remains uncompiled.
- ID24071: upload failed because `.../aspis-joint-20261019/sources/R1Z/` was absent; invoking `.../r1-privacy-build-integration-20261019/tools/run-joint.sh` failed with `No such file`. No scope or Lean attempt launched. Uncharged; next unused ID24072.
- Charged resume budget so far:71/100 Lean,10/20 Kani. Source rows discharged18/73. No checked shipped-source counterexample. No privacy-endpoint premise removal.

The binding local-lean.txt rule5 reserves build/launcher/monitoring repair to the lead. An asynchronous restoration/location question was presented to the user. Source preparation continues without host launches. The combined18-row candidate dictionary and five focused projection groups are PREPARED only, not compiled.

Resume after restoration: compile corrected PV_CB_Op105Funs with next unused ID, then PV_CB_Op105Exact; continue107,109,118 in ascending order. Compile the joint dictionary and focused projection groups after source targets pass, and perform one final axioms/dependency audit. Never label the target established.
