"""Retain every non-probe failing property and selected trace assignments."""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
for ident in sys.argv[1:]:
 D=E/'host'/ident
 docs=json.loads((D/'trace-summary.json').read_text());rows=[]
 for doc in docs:
  for f in doc['failed']:
   if f.get('sourceLocation',{}).get('propertyClass')=='reachability_check':continue
   trace=f.get('trace',[])
   # Keep original step numbers so a compact excerpt is tied to the full trace.
   selected=[]
   for i,s in enumerate(trace):
    loc=s.get('sourceLocation',{});lhs=s.get('lhs','')
    if s.get('stepType')=='failure' or (s.get('stepType')=='assignment' and (loc.get('file','') in ['lib.rs','src/indexed.rs','src/sealed.rs'] or lhs in ['n','i','k','b','j','len','r.len','index','query','wrong','lane','byte_index','byte_query','observed'])):
     selected.append({'trace_step':i,'stepType':s.get('stepType'),'lhs':lhs,'value':s.get('value'),'location':loc,'property':s.get('property')})
   rows.append({'property':f.get('property'),'description':f.get('description'),'location':f.get('sourceLocation'),'trace_steps':len(trace),'excerpt':selected})
 (D/'trace-excerpt.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(ident,[(r['description'],r['location'].get('line'))for r in rows])
