"""One-time additive registration; the validator recomputes every certificate."""
from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;p=E/'NEO_validate.py';s=p.read_text()
s=s.replace('crows,cedges=cells.expected(base,nen.q.check_receipt)','crows,cedges=cells.expected(base,nen.q.check_receipt)\n import NEO_tail_certificates as tail\n trows,tedges=tail.expected(base,nen.q.check_receipt)')
s=s.replace("'NEO_cell_row_certificates'},'unexpected edge artifact keys'","'NEO_cell_row_certificates','NEO_tail_row_certificates'},'unexpected edge artifact keys'")
s=s.replace("require(edges['NEO_cell_row_certificates']==crows,'unregistered cell getter certificate')","require(edges['NEO_cell_row_certificates']==crows,'unregistered cell getter certificate')\n require(edges['NEO_tail_row_certificates']==trows,'unregistered checked-index/opening certificate')")
s=s.replace("if original['edge'] in cedges:expected.update(cedges[original['edge']])","if original['edge'] in cedges:expected.update(cedges[original['edge']])\n  if original['edge'] in tedges:expected.update(tedges[original['edge']])")
marker=" require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')"
s=s.replace(marker,''' for key,cert in trows.items():
  row=index[key];require(row['composed_status']=='OPEN' and not row['caller_domain_obligations'],'tail row collision or unexpected callee')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::'+cert['function']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Actual all-input checked constructor / complete physical opening versus independent extracted reference; exact full Result and same caller carrier/frame')
  row['named_hypotheses']=[dict(name='NEO::'+cert['function']+'.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
'''+marker)
s=s.replace('set(grows)|set(crows)','set(grows)|set(crows)|set(trows)')
s=s.replace("delta['total_closed']==126 and delta['q_closed']==104 and delta['edge_closed']==122","delta['total_closed']==130 and delta['q_closed']==108 and delta['edge_closed']==124");p.write_text(s)
sys.path.insert(0,str(E));import NEO_validate as v,NEO_tail_certificates as t
rows,edges=t.expected(v.baseline(),v.nen.q.check_receipt);e=v.obj(E/'NEO_EDGES.json');e['NEO_tail_row_certificates']=rows
for edge in e['edges']:
 if edge['edge'] in edges:edge.update(edges[edge['edge']])
(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(126,104,122)','(130,108,124)');s=s.replace(' def mutate_parser(self,change):',''' def test_tail_all_input_constructor_domain(self):
  e=copy.deepcopy(self.edges);e['NEO_tail_row_certificates']['TX1:063']['domain']='Only canonical inputs'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_tail_opening_complete_allocation(self):
  e=copy.deepcopy(self.edges);e['NEO_tail_row_certificates']['TX1:085']['domain']='A smaller unrelated buffer'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_tail_missing_result(self):
  e=copy.deepcopy(self.edges);e['NEO_tail_row_certificates']['TX2:044']['parts'].remove('result')
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_tail_missing_callsite(self):
  e=copy.deepcopy(self.edges);next(x for x in e['edges'] if x['edge'].endswith(' -> crates/aspis-r1-cost-probe/src/candidate.rs::opening'))['certificate']['parts'].remove('native_callsite_association')
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def mutate_parser(self,change):''');p.write_text(s)
