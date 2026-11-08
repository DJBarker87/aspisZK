# Bootstrap/review aid only: final accepted Lean sources are authoritative.
# This emits intermediate source, not a release/regeneration command.
"""Reassemble the retained prefix with arbitrary entry world; reuse generic segments.
No emitted source program, step, table, environment or loop is generated here.
The output is reviewed and compiled in dependency groups, never blindly replayed.
"""
from pathlib import Path
import re
R=Path(__file__).resolve().parents[3]
P=R/'lean'
selected={
'TlsAt54':['at54'],
'TlsNative15':['physical','active','value'],
'TlsBound15':['answer'],
'TlsDelivery15':['after','transition'],
'TlsAt55':['at55','ordinary','context','consume','original55'],
'TlsAt58':['at58','original58','first_native','world58'],
'Tls59Data15':['after','at59','nonnative'],
'Tls277Delivery15':['transition'],
'TlsAt59':['context','consume','original59'],
'TlsAt63':['at63','original63','state63','issued63','consumed63','world63','entry'],
'Tls64Data16':['after','at64','nonnative'],
'Tls278Delivery16':['transition'],
'TlsAt64':['context','consume','original64'],
'TlsAt67':['at67','original67','state67','issued67','consumed67','world67','entry'],
'Tls68Data16':['after','at68','nonnative'],
'Tls279Delivery16':['transition'],
'TlsAt68':['context','consume','original68'],
'TlsAt75':['at75','original75','state75','consumed75'],
'TlsAt84':['at84','stage75','dereference','original84','state84','issued84','consumed84'],
'Tls18Reached16':['active'],
'Tls85Data16':['after','at85','ordinary'],
'Tls18Delivery16':['transition'],
'TlsAt85':['context','consume','original85'],
}
ns=lambda m:'PV_LIB_SPEC_World18_'+m
mapping={f'PV_LIB_SPEC_{m}.{n}':f'({ns(m)}.{n} e)' for m,names in selected.items() for n in names}
mapping['PV_LIB_SPEC_TlsAt54.original54']='(PV_LIB_SPEC_Prefix54World18.original54 e.world)'
# source module order is the already compiled dependency order
chunks=[list(selected)[:5],list(selected)[5:9],list(selected)[9:13],list(selected)[13:17],list(selected)[17:]]
for k,mods in enumerate(chunks):
 out='import PV_LIB_SPEC_'+('Prefix54World18' if k==0 else f'TlsWorld18_{k}')+'\nimport PV_LIB_SPEC_TlsAt85\nset_option autoImplicit false\nnoncomputable section\n'
 for m in mods:
  text=(P/f'PV_LIB_SPEC_{m}.lean').read_text();namespace='PV_LIB_SPEC_'+m
  header=text[text.index('namespace '+namespace)+len('namespace '+namespace):]
  header=header[:re.search(r'^\s*(?:/--|def |theorem )',header,re.M).start()]
  # keep opens of OLD data; names of copied declarations are rewritten below
  out+='\nnamespace '+ns(m)+'\n'+header+'\nopen '+namespace+'\n'
  names=re.findall(r'^(?:def|theorem) (\w+)',text,re.M)
  bare={n:namespace+'.'+n for n in names}
  for match in re.finditer(r'^open (PV_LIB_SPEC_\w+)(?: \(([^)]+)\))?\s*$',text,re.M):
   module,items=match.groups()
   if items:items=items.split()
   else:
    path=P/(module+'.lean')
    items=re.findall(r'^(?:def|theorem) (\w+)',path.read_text(),re.M) if path.exists() else []
   for n in items:bare.setdefault(n,module+'.'+n)
  decls=list(re.finditer(r'^(def|theorem) (\w+)\b',text,re.M))
  for i,d in enumerate(decls):
   typ,name=d.groups()
   if name not in selected[m]:continue
   stop=decls[i+1].start() if i+1<len(decls) else text.index('#print axioms')
   code=text[d.end():stop].split('#print axioms')[0]
   # Strip trailing docs describing the next declaration.
   code=re.sub(r'\n/--[\s\S]*$', '',code).rstrip()
   # Qualify bare imported data/lemmas, without touching already qualified identifiers.
   pattern=r'(?<![\w.])(?:'+'|'.join(sorted(map(re.escape,bare),key=len,reverse=True))+r')(?![\w])'
   code=re.sub(pattern,lambda h:bare[h[0]],code)
   code=code.replace('PV_LIB_SPEC_Entry14.state','e.world').replace('PV_LIB_SPEC_Entry14.input','(PV_LIB_SPEC_EntryWorld18.input e.world)')
   for old,new in sorted(mapping.items(),key=lambda v:-len(v[0])):
    code=re.sub(r'(?<![\w.])'+re.escape(old)+r'\b',lambda h:new,code)
   if m=='TlsNative15' and name=='physical':code=code[:code.index(':=')]+':= e.active'
   if name=='entry':code=code[:code.index(':=')]+':= e.pre'
   code=re.sub(r'unfold \((PV_LIB_SPEC_World18_\w+\.\w+) e\)',r'unfold \1',code)
   out+=typ+' '+name+' (e : PV_LIB_SPEC_EntryWorld18.Entry)'+code+'\n\n#print axioms '+name+'\n\n'
  out+='end '+ns(m)+'\n'
 (P/f'PV_LIB_SPEC_TlsWorld18_{k+1}.lean').write_text(out)
