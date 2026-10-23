#!/usr/bin/env python3
"""Normalize the retained J10800 receipts; never launches a compiler."""
import hashlib, json, re, subprocess
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SRC = ROOT / 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean'
out = (HERE / 'out-10800.log').read_text()
timing = (HERE / 'time-10800.log').read_text()
deps = json.loads((HERE / 'dependencies-10800.json').read_text())
def field(pattern):
    return re.search(pattern, timing).group(1).strip()
axioms = re.findall(r"^'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)", out, re.M)
assert len(axioms) == 2
assert out.count('exit=0') == 1
assert 'error:' not in out
r = dict(attempt=10800, environment='J', module='R1Z.PrivacyR1HeadlineDeployedReal',
         source_revision='7669f7d8785be416d8dbbf0611fd7a16463e757a', source_sha256=hashlib.sha256(SRC.read_bytes()).hexdigest(),
         deps_fingerprint=deps['deps_fingerprint'], dependencies=deps['imports'],
         command='sh /home/dombarker/project-offloads/codex-cx-priv-restate-20261023/run-joint.sh 10800 R1Z/PrivacyR1HeadlineDeployedReal J 7000 7 43ba1775696887d0',
         exit=0, wall=field(r'Elapsed .*: (\S+)'),
         peak_rss_kib=int(field(r'Maximum resident set size \(kbytes\): (\d+)')),
         swaps=int(field(r'Swaps: (\d+)')), axioms=axioms, errors=[],
         warnings=[line for line in out.splitlines() if 'warning:' in line],
         memory_high_gib=5, memory_max_gib=7, memory_swap_max=0, lean_memory_limit_mb=7000,
         aggregate_populated_before_gib=24, aggregate_with_job_gib=31,
         target_kind='focused endpoint plus its projection lemma; cached imported closure',
         existing_shared_sources_overwritten=False, coherent_release_replay=False)
assert r['source_sha256'] == '0374f534aaadcfcf3855dc9402feaae176f93f11687b0fab7773b075599e7b42'
(HERE / 'attempts.jsonl').write_text(json.dumps(r)+'\n')
print(json.dumps(r, indent=2))
