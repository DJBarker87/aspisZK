# PIN2 FINAL receipts (Stream C lead, 2026-11-11)

zk-72 declared PIN2 final: pin c7593d23fdc56fcee9a9df1628d5f63b52ac7a95, tools d7142292c480303e90c9c96e7f4c60dde9a87961.

- S1 artefact gate FINAL: PIN2_ARTEFACT_GATE_FINAL.json / .md, produced by evidence/prov-p9c-20261110/PCXS_pin2_s1_gate.py on the final full heads; byte-identical to the provisional report (sha256 46b826a1... / f8f84996...). NOT_NAMED 0; programs/aspis-pool equal to b936275.
- Host src for S3 verified equal to git archive of the final pin (4,207 files, diff -rq empty).
- S3 ELF FINAL builds PCXS_F001 (default), PCXS_F002 (retarget, Pool 37hdATMk..., registry 9pWwAc...), PCXS_F003 (aspis-upload), same recipe and workspace as B001-B003: sha256 5f083ab3... / 2284239e... / 9b2ab3d4..., byte-identical to B001-B003; Cargo.lock 7cc53354... unchanged in all six before/after files. The .so files stay on the host (out/PCXS_F00*/artifacts).
- S5 client reproducibility: attempt 2 of PCXT_build_ctr.sh, byte-identical to attempt 1 (devnet_spend 22101cfa..., pv_client_gate feb32b5c...).
