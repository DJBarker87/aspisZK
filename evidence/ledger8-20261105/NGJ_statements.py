from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;I=E.parent/'slice-s-join-20261105'
items=[dict(section='S',attempt='NGJ_L038',names=[r['theorem'] for r in json.loads((I/'NGI_ROOT_NAMES.json').read_text())]),dict(section='Q',attempt='NGJ_L039',names=re.findall(r'^#check @([\w.]+)',(E/'NGJ_ROOT_Q.lean').read_text(),re.M))]
text='''## Exact S and Q theorem statements

These are fresh full kernel-loaded `#check @name` quotations from the passing verifier aggregate, with explicit arguments, full names and universes. Every named root also appears in the authoritative raw ax2 audit. The exact `#print axioms` lines follow each statement. Universe annotations do not add axiom constants. Source/native association remains the validated hybrid packet with caller-established domains and retained trust; no quantifier, hypothesis or conclusion is changed here. All seven S statements match NGI's prior quotation exactly. Q's query_loop TX1/TX2 and for_range model/native-association roots are quoted separately; query_values source/result is supporting composition, not a third Q root.
'''
records=[]
for group in items:
 log=(E/group['attempt']/'stdout.log').read_text()
 text+='\n### Slice '+group['section']+'\n'
 for n in group['names']:
  start=re.search(r'^@?'+re.escape(n)+r'(?:\.\{[^}]*\})? :',log,re.M).start();m=re.search("'"+re.escape(n)+"' (?:depends on axioms:\\s*\\[[^\\]]*\\]|does not depend on any axioms)",log[start:]);assert m,n
  quote=log[start:start+m.end()]
  if group['section']=='S':
   prior=(I/'NGI_L030/stdout.log').read_text();a=prior.index('@'+n+' :');mm=re.search("'"+re.escape(n)+"' (?:depends on axioms:\\s*\\[[^\\]]*\\]|does not depend on any axioms)",prior[a:]);assert quote==prior[a:a+mm.end()],n
  records.append(dict(section=group['section'],name=n,attempt=group['attempt'],quote_sha256=hashlib.sha256(quote.encode()).hexdigest(),axiom_line=m[0]))
  text+='\n`'+n+'` ('+group['attempt']+').\n\n```lean\n'+quote+'\n```\n'
p=E/'NGJ_STATEMENT.md';old=p.read_text();a=old.index('## Exact S and Q theorem statements');b=old.index('## Missing complete transaction and Pool joins',a);p.write_text(old[:a]+text+'\n'+old[b:]);(E/'NGJ_STATEMENT_QUOTES.json').write_text(json.dumps(records,indent=1)+'\n')
print('Quoted',len(records),'existing roots/support statements; all 7 S statements match NGI exactly')
