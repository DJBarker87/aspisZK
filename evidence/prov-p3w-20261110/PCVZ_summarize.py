#!/usr/bin/env python3
import json,glob,os
rows=[]
for r in sorted(glob.glob('PCVZ_L[0-9][0-9][0-9]/receipt.json')):
    x=json.load(open(r))
    rows.append(dict(attempt=x['attempt'],module=x['module'],exit=x['exit_status'],wall_s=round(x['wall_seconds'],2),peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],source_tree_dirty=x.get('source_tree_dirty'),print_axioms=[a.replace('\n','') for a in x['print_axioms']],sha256=x['source_hashes']))
json.dump(rows,open('PCVZ_SCOPES.json','w'),indent=1)
for r in rows: print(r['attempt'],r['module'],r['exit'],r['wall_s'])
