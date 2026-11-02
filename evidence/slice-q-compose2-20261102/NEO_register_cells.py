from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;p=E/'NEO_validate.py';s=p.read_text()
s=s.replace("gedges=gedge.expected(base,nen.q.check_receipt)","gedges=gedge.expected(base,nen.q.check_receipt)\n import NEO_cell_certificates as cells\n crows,cedges=cells.expected(base,nen.q.check_receipt)")
s=s.replace("'NEO_getter_row_certificates'},'unexpected edge artifact keys'","'NEO_getter_row_certificates','NEO_cell_row_certificates'},'unexpected edge artifact keys'")
s=s.replace("require(edges['NEO_getter_row_certificates']==grows,'unregistered borrowed getter certificate')","require(edges['NEO_getter_row_certificates']==grows,'unregistered borrowed getter certificate')\n require(edges['NEO_cell_row_certificates']==crows,'unregistered cell getter certificate')")
s=s.replace("if original['edge'] in gedges:expected.update(gedges[original['edge']])","if original['edge'] in gedges:expected.update(gedges[original['edge']])\n  if original['edge'] in cedges:expected.update(cedges[original['edge']])")
marker=" require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')"
s=s.replace(marker,''' for key,cert in crows.items():
  row=index[key];require(row['composed_status']=='OPEN' and not row['caller_domain_obligations'],'cell row collision or unexpected callee')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::'+cert['function']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Actual indexed scalar/record helper versus independent extracted safe reference, exact coherent op12/op13 and lossless carrier/frame; caller bounds proved')
  row['named_hypotheses']=[dict(name='NEO::'+cert['function']+'.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
'''+marker)
s=s.replace("sorted(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows))","sorted(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows)|set(crows))").replace("len(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows))","len(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows)|set(crows))")
s=s.replace("delta['total_closed']==118 and delta['q_closed']==96 and delta['edge_closed']==116","delta['total_closed']==122 and delta['q_closed']==100 and delta['edge_closed']==118");p.write_text(s)
sys.path.insert(0,str(E));import NEO_validate as v,NEO_cell_certificates as c
rows,edges=c.expected(v.baseline(),v.nen.q.check_receipt);e=v.obj(E/'NEO_EDGES.json');e['NEO_cell_row_certificates']=rows
for edge in e['edges']:
 if edge['edge'] in edges:edge.update(edges[edge['edge']])
(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(118,96,116)','(122,100,118)');s=s.replace(' def mutate_parser(self,change):',''' def test_cell_canonical_only_domain(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_cell_row_certificates'].values()))['domain']='canonical values only'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_cell_missing_carrier(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_cell_row_certificates'].values()))['lean_evidence'].pop()
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def mutate_parser(self,change):''');p.write_text(s)
