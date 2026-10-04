# Generator checks

- python3 generator/generate-preflight.py --check  # PASS (check OK)
- for i in $(seq 0 32); do python3 generator/generate-r799-remaining.py --chunk "$i" --check; done  # PASS (33 checks)
- R797 renderer check: NOT AVAILABLE; exact historical renderer was overwritten, so no substituted check was run
- R798 duplicate renderer check: NOT RUN after final coverage input changed; its exact source is retained only as duplicate-run provenance, not as selected evidence
