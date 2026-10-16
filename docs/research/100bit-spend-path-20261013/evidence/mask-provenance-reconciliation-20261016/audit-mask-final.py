import json
from pathlib import Path
from collections import Counter
ws=Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015')
q=json.loads(Path('/tmp/focused-recheck-queue.json').read_text())
counts=Counter(); report_count=0; nonstandard=[]; standard={'propext','Classical.choice','Quot.sound'}
for it in q['items']:
 n=it['order']
 if n<=49: label=f'queue144-{n:03d}'
 elif n==50: label='queue144-050-repair7'
 elif 51<=n<=64: label=f'queue144-{n:03d}'
 elif 65<=n<=73: label=f'queue144-repair7-{n:03d}'
 elif n==74: label='queue144-repair7-v6fix1-074'
 else: label=f'queue144-repair8-{n:03d}'
 d=ws/'attempts'/f"{label}-{it['module'].replace('.', '_')}"
 ax=json.loads((d/'axiom-reports.json').read_text())
 for item in ax:
  report_count+=1; axs=tuple(sorted(item.get('axioms',[]))); counts[axs]+=1
  extra=sorted(set(axs)-standard)
  if extra: nonstandard.append({'order':n,'module':it['module'],'declaration':item['declaration'],'axioms':axs,'extra':extra})
print(json.dumps({'reports':report_count,'axiom_set_counts':{';'.join(k):v for k,v in counts.items()},'nonstandard_report_count':len(nonstandard),'nonstandard_reports':nonstandard},indent=2))
