#!/usr/bin/env python3
"""NPH_: append one NPH_COMPILE.tsv row from an attempt receipt. Usage: NPH_compile_row.py NPH_Lnnn 'note'"""
import json,sys
a,note=sys.argv[1:3];r=json.load(open(f'{a}/receipt.json'))
ax=r.get('print_axioms',[]);import re
def ok(x):
 m=re.search(r'depends on axioms: \[(.*)\]$',x)
 return 'does not depend on any axioms' in x or (m is not None and set(s.strip() for s in m.group(1).split(','))<= {'propext','Classical.choice','Quot.sound'})
std=[x for x in ax if ok(x)]
row=[a,r['module'],str(r['exit_status']),str(round(r['wall_seconds'],3)),str(r['peak_rss_kib']),str(r.get('cgroup_memory_peak_bytes','')),str(r['swaps']),
 'MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64 lean -j1 -M7000 timeout 180s',list(r['source_hashes'].values())[0] if isinstance(r['source_hashes'],dict) else '',
 r['source_revision']+(' (dirty worktree)' if r['source_tree_dirty'] else ''),f'{len(ax)} #print axioms lines; {len(std)} within [propext, Classical.choice, Quot.sound]; {len(ax)-len(std)} with sorryAx/other',note]
open('NPH_COMPILE.tsv','a').write('\t'.join(row)+'\n');print('\t'.join(row))
