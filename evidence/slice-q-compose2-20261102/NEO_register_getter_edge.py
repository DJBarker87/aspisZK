from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;p=E/'NEO_validate.py';s=p.read_text()
s=s.replace("grows=gcert.expected(base,nen.q.check_receipt)","grows=gcert.expected(base,nen.q.check_receipt)\n import NEO_getter_edge as gedge\n gedges=gedge.expected(base,nen.q.check_receipt)")
s=s.replace("if original['edge'] in oedges:expected.update(oedges[original['edge']])","if original['edge'] in oedges:expected.update(oedges[original['edge']])\n  if original['edge'] in gedges:expected.update(gedges[original['edge']])")
s=s.replace("delta['edge_closed']==115","delta['edge_closed']==116");p.write_text(s)
sys.path.insert(0,str(E));import NEO_validate as v,NEO_getter_edge as g
e=v.obj(E/'NEO_EDGES.json');expected=g.expected(v.baseline(),v.nen.q.check_receipt)
for edge in e['edges']:
 if edge['edge'] in expected:edge.update(expected[edge['edge']])
(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(118,96,115)','(118,96,116)');s=s.replace(' def mutate_parser(self,change):',''' def test_getter_edge_no_copied_value(self):
  e=copy.deepcopy(self.edges);x=next(x for x in e['edges'] if x['edge'].endswith(' -> crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query'));x['certificate']['parts'].remove('same_inputs_result')
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def mutate_parser(self,change):''');p.write_text(s)
