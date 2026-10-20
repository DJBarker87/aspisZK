#!/usr/bin/env python3
"""Compact immutable receipts, no full census or binary artifacts."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'docs/research/100bit-spend-path-20261013/evidence/r22-overflow2-20261021'
subprocess.run(['rsync','-a','--include=*/','--include=receipt.json','--exclude=*','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-r22-overflow2-20261021/receipts/',str(OUT/'attempts')+'/'],check=True)
rows=[]
for p in sorted((OUT/'attempts').glob('*/receipt.json')):
    r=json.loads(p.read_text());rows.append(r)
(OUT/'summary.tsv').write_text('attempt\ttarget\texit\twall_seconds\tpeak_rss_kib\tswaps\tverification_success\n'+''.join(f"{r['attempt']}\t{r['command'][r['command'].index('--harness')+1]}\t{r['exit_status']}\t{r['wall_seconds']:.3f}\t{r['peak_rss_kib']}\t{r['swaps']}\t{r['verification_success']}\n" for r in rows))
print(json.dumps({'attempts':len(rows),'successful':sum(r['verification_success'] for r in rows)}))
