#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
b=Path(__file__).resolve().parent;root=b.parents[4];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=root/'docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean'
old=b.parent/'r18-current-framing-closure-20261016/runs/framing-duplex-a/source.lean';s=old.read_text()
changes=[('    have hcard : (0 : ℚ) < (Fintype.card State : ℚ) := by positivity','    have hcard : (0 : ℚ) < (Fintype.card State : ℚ) := by\n      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card State)'),('    rw [mean_congr hz, mean_const]\n    positivity','    rw [mean_congr hz, mean_const]\n    exact div_nonneg\n      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (Nat.cast_nonneg Qtot))\n      (Nat.cast_nonneg (Fintype.card State))'),('  have hε : (0 : ℚ) ≤ (2 * Qtot : ℚ) / (256 ^ 32 : ℚ) := by positivity','  have hε : (0 : ℚ) ≤ (2 * Qtot : ℚ) / (256 ^ 32 : ℚ) := by\n    exact div_nonneg\n      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (Nat.cast_nonneg Qtot))\n      (pow_nonneg (by norm_num : (0 : ℚ) ≤ 256) 32)')]
for before,after in changes:
 assert s.count(before)==1;s=s.replace(before,after)
assert s.encode()==p.read_bytes()
a='framing-duplex-b';d=b/'runs'/a;r=json.loads((d/'receipt.json').read_text())
assert r['exit_status']==0 and p.read_bytes()==(d/'source.lean').read_bytes()
assert r['source_sha256']==sha(p) and r['runner_sha256']==sha(d/'runner.py')
assert r['input_manifest_sha256']==sha(b/('input-manifest-'+a+'.json'))
assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
assert r['memory_events_before']==r['memory_events_after']
assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
assert r['runtime_sha256'] and '4.32.0' in r['lean_version']
log=(d/'lean.log').read_text();reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
assert len(reports)==1 and reports[0][0]=='FS2.Duplex.coll_mass'
for _,ax in reports:assert set(x.strip() for x in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log and 'error:' not in log
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,q=line.split('  ',1);assert sha(b/q)==h,q
print('PASS: exactly three proof-body substitutions; focused Duplex/standard-only audit; retained runtime/resource/input/output pins')
