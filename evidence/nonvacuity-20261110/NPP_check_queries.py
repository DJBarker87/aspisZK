#!/usr/bin/env python3
"""NPP_: offline check of the probe's H table (faithfulness item F-c for TX1).
Usage: python3 -I NPP_check_queries.py <NPP_L012/stdout.log> <out-table.tsv.xz>
Every line `NPP_Q <query-hex> <digest-hex>` is a query the interpreted model issued to H; each
digest is recomputed with hashlib.sha256. Writes the deduplicated table (query, digest) and prints
a JSON summary."""
import sys, hashlib, json, lzma
qs = []
for line in open(sys.argv[1]):
    if line.startswith('NPP_Q '):
        parts = line.split()
        q = parts[1] if len(parts) == 3 else ''
        qs.append((q, parts[-1]))
bad = [i for i, (q, d) in enumerate(qs) if hashlib.sha256(bytes.fromhex(q)).hexdigest() != d]
table = {}
for q, d in qs: table.setdefault(q, d)
with lzma.open(sys.argv[2], 'wt') as f:
    for q, d in table.items(): f.write(f'{q}\t{d}\n')
lens = sorted({len(q) // 2 for q in table})
print(json.dumps({'queries_logged': len(qs), 'distinct_queries': len(table), 'digest_mismatches': len(bad),
                  'query_lengths_bytes': lens[:20], 'total_query_bytes': sum(len(q)//2 for q in table)}, indent=1))
