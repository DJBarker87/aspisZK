# NMC replay inputs

Target not yet established. Current harnesses live only in the retained host scratch tree; the repository carries NMC_HARNESSES.patch plus exact input hashes. The patch is relative to the verified NLU scratch predecessor in NMC_PREDECESSOR_SOURCE_PINS.json. Its reverse-apply check and current source hashes are recorded by NMC_patch_export. NMC_patch_inputs.py reconstructs the two modules from the patch and rejects hash differences.

Historical attempts replay from their immutable receipt/sources snapshots, including the original raw harness inputs retained AS RECEIPT INPUTS. Their root configuration files are historical; NMC_run refuses resubmission. Never use current inputs to attribute a historical pass to a changed source. Retired K001/K002/K021/K039/K040 shapes are not rerun unchanged.

The actual frozen verifier bodies, deployed features and lock are checked before every native run. No source under the repository's crates/ or programs/ changed; only host scratch cfg(kani) modules were added. No SBF/ELF rebuild trigger occurred. No binaries, objects or keys are committed. Caches/TMPDIR/target are retained; only explicitly identified dead solver temporaries may be cleaned after all native runs.
