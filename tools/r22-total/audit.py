#!/usr/bin/env python3
"""Read-only signature census. Labels are conservative screening, not proof replay."""
import hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
B=ROOT/'docs/research/100bit-spend-path-20261013'
OUT=B/'evidence/r22-total-20261021'
paths=set((B/'lean').rglob('*.lean'))
paths.update((B/'lean-candidates').rglob('*.lean'))
rows=[]
for p in sorted(paths):
    if any(x in p.parts for x in ('diagnostics','worker-archive','worker-archives','raw-generated')): continue
    txt=p.read_text()
    # Retain every statement, rather than relying on filenames containing Total.
    for m in re.finditer(r'(?m)^(?:private |protected )?(?:theorem|lemma)\s+(\S+)',txt):
        end=txt.find(':=',m.end())
        if end<0: continue
        sig=txt[m.start():end].strip()
        if len(sig)>25000: continue
        runtime=bool(re.search(r'\b(?:ok|fail|Result|source_refines|total)\b',sig))
        hypotheses=bool(re.search(r'[({]\s*h\w*\s*:',sig))
        form='OTHER'
        reason='No unconditional successful extracted execution identified by signature screen.'
        if runtime and hypotheses:
            form='ACCEPTED-ONLY'; reason='Explicit hypothesis; inspect caller discharge and whether this is execution or model algebra.'
        elif re.search(r'=\s*(?:\.ok|ok)\b',sig) and not hypotheses:
            form='TOTAL-CANDIDATE'; reason='Success-shaped conclusion; manually check all dependent/implicit premises and source identity before R22.'
        rows.append(dict(path=str(p.relative_to(ROOT)),line=txt.count('\n',0,m.start())+1,
            theorem=m.group(1),signature=sig,screen=form,reason=reason,
            source_sha256=hashlib.sha256(txt.encode()).hexdigest()))
OUT.mkdir(parents=True,exist_ok=True)
(OUT/'signature-census.tsv').write_text('path\tline\ttheorem\tscreen\tsource_sha256\n'+''.join('\t'.join(str(r[k]) for k in ('path','line','theorem','screen','source_sha256'))+'\n' for r in rows))
summary={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'scope':'All non-diagnostic Lean and lean-candidates theorem signatures; screen labels are not audited classifications.',
 'files':len(set(r['path'] for r in rows)),'statements':len(rows),
 'counts':{f:sum(r['screen']==f for r in rows) for f in sorted(set(r['screen'] for r in rows))}}
(OUT/'census-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
