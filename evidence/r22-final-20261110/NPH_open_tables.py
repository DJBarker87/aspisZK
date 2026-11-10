#!/usr/bin/env python3
"""NPH_: print the open-definition table (section 3), the by-class line and the row-ID appendix (section 6)
of NPH_R22_FINAL_COUNTS.md from NPH_R22_CONE.json (read-only)."""
import json,collections,sys
c=json.load(open('NPH_R22_CONE.json'))
J=lambda e:(e.get('nph_judgment') or '').split(' ')[0].rstrip(':')
ex=[e for e in c['definitions'] if e['body_class'] in ('CHECKED','MIXED') and J(e)!='NOT_EXECUTED']
op=[e for e in ex if J(e) in ('OPEN','DOMAIN_LEMMA_PROVED')]
dep=collections.defaultdict(set)
for e in op:
  for r in e['rows']:dep[r].add(e['definition'])
only=collections.Counter(next(iter(s)) for s in dep.values() if len(s)==1)
op.sort(key=lambda e:(-e['n_rows'],e['definition']))
part=sys.argv[1] if len(sys.argv)>1 else 'table'
if part=='table':
  print('| Rows | Only blocker | Definition | Pattern class | What closes it |\n|---:|---:|---|---|---|')
  for e in op:print(f"| {e['n_rows']} | {only[e['definition']]} | `{e['definition']}` | {e.get('nph_pattern_class','')} | {e.get('nph_open_next_step','')} |")
  cl=collections.Counter(e.get('nph_pattern_class','') for e in op)
  print('\nBy class: '+'; '.join(f'{k} {v}' for k,v in cl.most_common())+'.')
  print(f"\nExposure structure: {sum(1 for s in dep.values() if len(s)==1)} rows depend on exactly one open definition.")
else:
  for e in op:print(f"- `{e['definition']}` ({e['n_rows']}): "+', '.join(e['rows']))
