#!/bin/sh
set -eu
cd /Users/dominic/ZK/.worktrees/cx-replay-tops2
python3 -u evidence/replay-tops2-20261027/RPu_post.py FJp
python3 evidence/replay-tops2-20261027/RPu_results.py
python3 evidence/replay-tops2-20261027/RPu_closure_check.py
git add evidence/replay-tops2-20261027
git commit -q -m 'Replay and audit the FJp top on the pinned cohort'
python3 -u evidence/replay-tops2-20261027/RPu_replay.py 336
python3 -u evidence/replay-tops2-20261027/RPu_post.py FJu
python3 evidence/replay-tops2-20261027/RPu_results.py
python3 evidence/replay-tops2-20261027/RPu_closure_check.py
git add evidence/replay-tops2-20261027
git commit -q -m 'Replay and audit the FJu top on the pinned cohort'
python3 -u evidence/replay-tops2-20261027/RPu_replay.py 495
python3 evidence/replay-tops2-20261027/RPu_results.py
git add evidence/replay-tops2-20261027
git commit -q -m 'Advance the FJv coherent dependency frontier'
python3 -u evidence/replay-tops2-20261027/RPu_post.py batches
python3 evidence/replay-tops2-20261027/RPu_results.py
python3 evidence/replay-tops2-20261027/RPu_audit_results.py
python3 evidence/replay-tops2-20261027/RPu_receipt_index.py
