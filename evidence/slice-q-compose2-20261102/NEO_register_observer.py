from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;p=E/'NEO_validate.py';s=p.read_text()
s=s.replace("qrows,qedges=qcert.expected(base,nen.q.check_receipt)","qrows,qedges=qcert.expected(base,nen.q.check_receipt)\n import NEO_observer_certificates as ocert\n orows,oedges=ocert.expected(base,nen.q.check_receipt)")
s=s.replace("'NEO_q_row_certificates'},'unexpected edge artifact keys'","'NEO_q_row_certificates','NEO_observer_row_certificates'},'unexpected edge artifact keys'")
s=s.replace("require(edges['NEO_q_row_certificates']==qrows,'unregistered private-Q certificate')","require(edges['NEO_q_row_certificates']==qrows,'unregistered private-Q certificate')\n require(edges['NEO_observer_row_certificates']==orows,'unregistered observer certificate')")
s=s.replace("if original['edge'] in qedges:expected.update(qedges[original['edge']])","if original['edge'] in qedges:expected.update(qedges[original['edge']])\n  if original['edge'] in oedges:expected.update(oedges[original['edge']])")
marker=" require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')"
s=s.replace(marker,''' for key,cert in orows.items():
  row=index[key];require(row['composed_status']=='OPEN','observer row collision')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::deployed_mark_none'],active_support_receipts=[],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Adopted z(1) exact deployed None specialization and emitted no-effect port; historical function-pointer results remain quarantined')
  row['named_hypotheses']=[dict(name='NEO::deployed_mark_none.PacketDomain',statement=cert['domain'],discharged_by=cert['id'])]
  for o in row['caller_domain_obligations']:
   require(o['id'] in cert['external_obligations'],'observer missing unreachable occurrence')
   o.update(status='CLOSED',discharged_by=cert['id']+':'+o['id'])
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
'''+marker)
s=s.replace("sorted(PEER_ROWS|set(parsers)|set(qrows))","sorted(PEER_ROWS|set(parsers)|set(qrows)|set(orows))").replace("len(PEER_ROWS|set(parsers)|set(qrows))","len(PEER_ROWS|set(parsers)|set(qrows)|set(orows))")
s=s.replace("delta['total_closed']==114 and delta['q_closed']==92 and delta['edge_closed']==114","delta['total_closed']==116 and delta['q_closed']==94 and delta['edge_closed']==115")
p.write_text(s)
sys.path.insert(0,str(E));import NEO_validate as v,NEO_observer_certificates as o
rows,edges=o.expected(v.baseline(),v.nen.q.check_receipt)
e=v.obj(E/'NEO_EDGES.json');e['NEO_observer_row_certificates']=rows
for edge in e['edges']:
 if edge['edge'] in edges:edge.update(edges[edge['edge']])
(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(114,92,114)','(116,94,115)')
s=s.replace(' def mutate_parser(self,change):',''' def test_observer_native_pointer_credit(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_observer_row_certificates'].values()))['active_support_receipts']=['NBC_K001']
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_observer_missing_unreached_callback(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_observer_row_certificates'].values()))['external_obligations'].clear()
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def mutate_parser(self,change):''')
p.write_text(s)
