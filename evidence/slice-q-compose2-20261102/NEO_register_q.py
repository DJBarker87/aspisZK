from pathlib import Path
E=Path(__file__).resolve().parent
p=E/'NEO_validate.py';s=p.read_text()
s=s.replace("registered=own.expected(base,nen.q.check_receipt)","registered=own.expected(base,nen.q.check_receipt)\n import NEO_q_certificates as qcert\n qrows,qedges=qcert.expected(base,nen.q.check_receipt)")
s=s.replace("'NEO_parser_row_certificates'},'unexpected edge artifact keys'","'NEO_parser_row_certificates','NEO_q_row_certificates'},'unexpected edge artifact keys'")
s=s.replace("require(edges['NEO_parser_row_certificates']==parsers,'parser root certificate artifact drift')","require(edges['NEO_parser_row_certificates']==parsers,'parser root certificate artifact drift')\n require(edges['NEO_q_row_certificates']==qrows,'unregistered private-Q certificate')")
s=s.replace("expected=copy.deepcopy(new.get(original['edge'],original))", "expected=copy.deepcopy(new.get(original['edge'],original))\n  if original['edge'] in qedges:expected.update(qedges[original['edge']])")
marker=" require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')"
addition=''' for key,cert in qrows.items():
  row=index[key];require(row['composed_status']=='OPEN','private-Q row collision')
  for oid,call in cert['calls'].items():
   callee=call['callee'];children=[r for r in out['rows'] if r['function']==callee]
   # Leaf order is explicit below; checked_q comes after the two leaf roots.
   require(children and all(r['composed_status']=='CLOSED' for r in children),'private-Q open callee')
   require(row['function']+' -> '+callee in qedges,'private-Q missing real edge')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=[cert['claim_id']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Full raw private-Q reference/Result/frame with three exact unrestricted callee-domain associations')
  row['named_hypotheses']=[dict(name=cert['claim_id']+'.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['caller_domain_obligations']:
   require(o['id'] in cert['calls'] or o['id'] in cert['external_obligations'],'private-Q missing occurrence')
   o.update(status='CLOSED',discharged_by=cert['id']+':'+o['id'])
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
'''
# Ensure real bottom-up order independent of baseline row order (checked before limbs_of there).
addition=addition.replace("for key,cert in qrows.items():","for key,cert in sorted(qrows.items(),key=lambda item:item[1]['function'].endswith('::checked_q')):")
s=s.replace(marker,addition+marker)
s=s.replace("sorted(PEER_ROWS|set(parsers))","sorted(PEER_ROWS|set(parsers)|set(qrows))").replace("len(PEER_ROWS|set(parsers))","len(PEER_ROWS|set(parsers)|set(qrows))")
s=s.replace("delta['total_closed']==104 and delta['q_closed']==82 and delta['edge_closed']==111","delta['total_closed']==114 and delta['q_closed']==92 and delta['edge_closed']==114")
p.write_text(s)
import sys,json
sys.path.insert(0,str(E));import NEO_validate as v,NEO_q_certificates as q
rows,edges=q.expected(v.baseline(),v.nen.q.check_receipt)
e=v.obj(E/'NEO_EDGES.json');e['NEO_q_row_certificates']=rows
for edge in e['edges']:
 if edge['edge'] in edges:edge.update(edges[edge['edge']])
(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(104,82,111)','(114,92,114)')
s=s.replace(" def mutate_parser(self,change):",''' def test_q_raw_domain(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_q_row_certificates'].values()))['domain']='canonical inputs only'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_q_missing_call(self):
  e=copy.deepcopy(self.edges)
  c=next(c for c in e['NEO_q_row_certificates'].values() if c['calls']);c['calls'].clear()
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_q_wrong_native_pair(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_q_row_certificates'].values()))['native_pair'][0]='NBQ_K005'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def mutate_parser(self,change):''')
p.write_text(s)
