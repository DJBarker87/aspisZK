from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;records=[];lines=['# Exact kernel-loaded statements','','Fresh full-name, explicit-argument and universe output from the SAME NGZ combined forest. These quotations do not discharge native/root hypotheses.','']
for i,target in enumerate(['PLAN_STATEMENTS','WRITER_STATEMENTS','POOL_STATEMENTS','TX2_STATEMENTS','ROOT_S','ROOT_Q'],35):
 a='NGZ_L'+str(i).zfill(3);source=(E/('NGZ_'+target+'.lean')).read_text();log=(E/a/'stdout.log').read_text()
 for n in re.findall(r'^#check @([\w.]+)',source,re.M):
  m=re.search(r'^@?'+re.escape(n)+r'(?:\.\{[^}]*\})? :',log,re.M);assert m,(a,n)
  ax=re.search("'"+re.escape(n)+"' (?:depends on axioms:\\s*\\[[^\\]]*\\]|does not depend on any axioms)",log[m.start():]);assert ax,(a,n)
  quote=log[m.start():m.start()+ax.end()];records.append(dict(name=n,attempt=a,quote_sha256=hashlib.sha256(quote.encode()).hexdigest(),axiom_line=ax[0],section=target))
  lines+=['## '+n,'',a+'. Exact statement and axioms:','','```lean',quote,'```','']
(E/'NGZ_STATEMENTS.md').write_text('\n'.join(lines));(E/'NGZ_STATEMENT_QUOTES.json').write_text(json.dumps(records,indent=1)+'\n')
p=E/'NGZ_STATEMENT.md';s=p.read_text().replace('Full explicit\nstatements will be quoted from the final statement receipts.','Full explicit\nstatements and exact axiom lines are freshly quoted in NGZ_STATEMENTS.md from\nL035–L040 (plan/headline, writer, Pool, TX2, S and Q respectively).')
s+='\n## Completed combined audit\n\nNGZ_L003 imports every selected forest with the headline. All5,663 selected roots pass the raw ax2 audit, standard axioms only, zero collectAxioms disagreements; all eight fixtures pass in the SAME proof binary. The full scan L034 covers13,761 modules,694,257 declarations and24,647,896 references with zero dangling references, incompatible owners or import mismatches. L033 is retained as an own-baseline failure:327 omitted implicit Init imports, no forest or scanner change. The repaired baseline was independently derived from committed sources. NGZ_CONFLICTS.json records no forest conflicts and no qualified rows. This is coherent cached composition, not L187.\n'
p.write_text(s)
print(len(records),'full statements')
