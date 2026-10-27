"""Summarize charged bounded runs without promoting timeout/selector failures."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
t=json.loads((out/'TALLY.json').read_text());lines=['# Charged Kani run summary','','Bounds and exact commands are in each target.json and harness.rs.txt. Toolchains and source/dependency hashes remain separate from deployed ELF/RunJoin association.','','| run | exit | wall | reported peak KiB | swap | verdict |','|---|---:|---|---:|---:|---|']
for name in t['kani_charged']:
 r=json.loads((out/name/'collected-receipt.json').read_text());code=int(r['exit']);verdict='PASS (bounded harness only)' if code==0 else 'TIMEOUT; no verdict/counterexample; wrapper RSS excludes killed descendants' if code==124 else 'REJECTED; no equivalence verdict'
 lines.append(f"| {name} | {code} | {r['wall']} | {r['peak_rss_kib']} | {r['swap']} | {verdict} |")
lines+=['',f"Charged: {len(t['kani_charged'])}/10. Refused admissions are not charged. No stubs or force-soft substitutions were used. No checked ROW counterexample was obtained. `#print axioms`: N/A native runs; exact revisions are in each collected-receipt.json. Native array, SHA2-vendor and block-buffer-vendor harnesses were prepared but never run."]
(out/'KANI-SUMMARY.md').write_text('\n'.join(lines)+'\n');print(len(t['kani_charged']))
