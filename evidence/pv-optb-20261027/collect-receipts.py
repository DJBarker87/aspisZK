#!/usr/bin/env python3
"""Collect existing host evidence; never launches or repeats a compile."""
import json,pathlib,re,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
ROOT='/home/dombarker/project-offloads'
JOB=ROOT+'/codex-pv-optb-20261027'
if '--local' not in sys.argv:
 pre=f'python3 {ROOT}/codex-pv-l2-sim-20261026/reservation.py {JOB}/reservation-collect.json > {JOB}/reservation-collect.log 2>&1'
 subprocess.run(['ssh',HOST,pre],check=True)
 allowed=json.loads(subprocess.check_output(['ssh',HOST,f'cat {JOB}/reservation-collect.json']))['allowed']
 if not allowed: raise SystemExit('reservation refused; no evidence transfer')
 subprocess.run(['scp',f'{HOST}:{ROOT}/aspis-fs-generic-20261006/evidence/*41[89][0-9][0-9]*',str(P)],check=True)
 subprocess.run(['scp',f'{HOST}:{JOB}/reservation-*.json',str(P)],check=True)
 subprocess.run(['scp',f'{HOST}:{JOB}/reservation-*.log',str(P)],check=True)
 subprocess.run(['scp',f'{HOST}:{JOB}/probes/native/*.log',str(P/'native')],check=True)
 subprocess.run(['scp',f'{HOST}:{JOB}/probes/native/*.time',str(P/'native')],check=True)
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
rows=[]
for f in sorted(P.glob('out-*.log')):
 a=int(f.stem[4:]);o=f.read_text();t=(P/f'time-{a}.log').read_text()
 def field(label):
  m=re.search(re.escape(label)+r': (.*)',t);return m.group(1) if m else None
 module=(P/f'sha-{a}.txt').read_text().split()[1].split('/sources/')[1][:-5]
 if not re.search(r'^exit=(\d+)',o,re.M):
  print('incomplete', a); continue
 rows.append(dict(attempt=a,target=module,source_sha256=(P/f'sha-{a}.txt').read_text().split()[0],deps_fingerprint='none',source_revision=('5f979998ac918cd81b6f499b830bc1dcfce2f333 + source hash' if a<=41801 else ('03dae99a8b + source hash' if a <= 41827 else ('75a81f55dc + source hash' if a <= 41876 else ('a6a4468262ce28ddf1fdfa067d611f65da06ad13 + source hash' if a <= 41898 else (P/'AUDIT-PIN.txt').read_text().strip())))),collection_revision=revision,exit=int(re.search(r'^exit=(\d+)',o,re.M).group(1)),wall=field('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_KiB=int(field('Maximum resident set size (kbytes)')),swaps=int(field('Swaps')),axioms=re.findall(r"'[^'\n]+'(?: depends on axioms:\s*\[[^\]]*\]| does not depend on any axioms)",o),errors=[l for l in o.splitlines() if 'error' in l],caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,lean_M=7000)))
(P/'receipts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
(P/'TALLY.md').write_text(f'# Attempt tally\n\nLean: {len(rows)}/100. Kani: 0/6. IDs used: '+', '.join(str(r['attempt']) for r in rows)+f'. Next: {rows[-1]["attempt"]+1}. IDs 41813 and 41828 were preflight-only and are retired.\nThe last three compile attempts (98–100) are reserved for audit. No IDs reused.\n')
print([(r['attempt'],r['exit']) for r in rows])

rows=[]
for f in sorted((P/'native').glob('*.time')):
 t=f.read_text()
 def field(label):
  m=re.search(re.escape(label)+r': (.*)',t);return m.group(1) if m else None
 row=dict(target=f.stem,source_revision='5f979998ac918cd81b6f499b830bc1dcfce2f333 immutable source snapshot',exit=field('Exit status'),wall=field('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_KiB=field('Maximum resident set size (kbytes)'),swaps=field('Swaps'),axioms='N/A native experiment',scope='MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64',phase='optimized Rust compilation' if f.stem.startswith('build') else 'optimized prove_masked_attempt, fixed OS interpreter')
 rows.append(row)
(P/'native'/'receipts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
