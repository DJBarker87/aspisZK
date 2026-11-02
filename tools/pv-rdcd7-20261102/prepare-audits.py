"""Project only affected consumer queries; never replay unchanged unrelated rows."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdcd7-20261102'
s=(L/'PV_RDCD5_FocusedReplay.lean').read_text();a=s.index('theorem v197_corrected');b=s.index('#print axioms v197_corrected',a)+len('#print axioms v197_corrected');snippet=s[a:b]
p=L/'PV_RDCD5_V197ConsumerReplay.lean'
p.write_text('import R1Z.PV_RDCD5_V197Restored\nset_option autoImplicit false\nnamespace R1Z.PV_RDCD5_V197ConsumerReplay\nopen Aeneas Aeneas.Std Result\n'+snippet+'\nend R1Z.PV_RDCD5_V197ConsumerReplay\n')
mods=['PV_RDCD4_SliceRange194','PV_RDCD5_ParserRange','PV_RDCD4_TryArray194','PV_RDCD4_Endian194','PV_RDCD4_BytesSource','PV_RDCD4_ParserWindows','PV_RDCD4_V197','PV_RDCD5_ParserWindows','PV_RDCD5_V197','PV_RDCD5_ParserFlat','PV_RDCD5_ParserTransport','PV_RDCD5_ParserErrors','PV_RDCD5_V197Restored','PV_RDCD5_V197ConsumerReplay']
queries=[]
for m in mods:
 for n in re.findall(r'^#print axioms (\S+)',(L/(m+'.lean')).read_text(),re.M):
  full=n if n.startswith('R1Z.') else 'R1Z.'+m+'.'+n
  if full not in queries:queries.append(full)
out='import R1Z.PV_RDCD5_V197ConsumerReplay\n'
for n in queries:out+='#check @'+n+'\n#print axioms '+n+'\n'
(L/'PV_RDCD5_V197Audit.lean').write_text(out)
(L/'PV_RDCD5_V197Focused.lean').write_text('''import R1Z.PV_RDCD5_V197Audit
#check @R1Z.PV_RDCD5_V197Restored.parser_instance
#print axioms R1Z.PV_RDCD5_V197Restored.parser_instance
#check @R1Z.PV_RDCD5_V197Restored.native_window
#print axioms R1Z.PV_RDCD5_V197Restored.native_window
#check @R1Z.PV_RDCD5_V197Restored.input_frame
#print axioms R1Z.PV_RDCD5_V197Restored.input_frame
''')
(L/'PV_RDCD5_V197FrozenManifest.lean').write_text('''import R1Z.PV_RDCD5_V197Focused
#check @R1Z.PV_RDCD5_V197Restored.parser_instance
#print axioms R1Z.PV_RDCD5_V197Restored.parser_instance
#check @R1Z.PV_RDCD5_ParserTransport.quartic
#print axioms R1Z.PV_RDCD5_ParserTransport.quartic
#check @R1Z.PV_RDCD5_V197ConsumerReplay.v197_corrected
#print axioms R1Z.PV_RDCD5_V197ConsumerReplay.v197_corrected
''')
(E/'consumer-audit-projection.json').write_text(json.dumps(dict(modules=mods,queries=queries,scope='All affected parser declarations and exact corrected v197 replay proof. Audit-only consumers are checked through their affected declaration queries; no unchanged V201/V220/V233/V236/V237 suite is rerun.',consumer_source='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDCD5_FocusedReplay.lean',source_sha256=hashlib.sha256(s.encode()).hexdigest(),exact_theorem_snippet=snippet,snippet_sha256=hashlib.sha256(snippet.encode()).hexdigest(),namespace_mapping={'R1Z.PV_RDCD5_FocusedReplay':'R1Z.PV_RDCD5_V197ConsumerReplay'},no_statement_or_proof_edit=True),indent=2)+'\n')
print(len(queries),'exact declaration type/summary-axiom queries; raw NEP audit remains separate')
