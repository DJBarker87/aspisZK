from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;p=E/'NEO_validate.py';s=p.read_text()
s=s.replace("orows,oedges=ocert.expected(base,nen.q.check_receipt)","orows,oedges=ocert.expected(base,nen.q.check_receipt)\n import NEO_getter_certificates as gcert\n grows=gcert.expected(base,nen.q.check_receipt)")
s=s.replace("'NEO_observer_row_certificates'},'unexpected edge artifact keys'","'NEO_observer_row_certificates','NEO_getter_row_certificates'},'unexpected edge artifact keys'")
s=s.replace("require(edges['NEO_observer_row_certificates']==orows,'unregistered observer certificate')","require(edges['NEO_observer_row_certificates']==orows,'unregistered observer certificate')\n require(edges['NEO_getter_row_certificates']==grows,'unregistered borrowed getter certificate')")
marker=" require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')"
s=s.replace(marker,''' for key,cert in grows.items():
  row=index[key];require(row['composed_status']=='OPEN' and not row['caller_domain_obligations'],'getter row collision or unexpected callee')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::geometry_for_query'],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Actual full borrowed getter against independent safe reference, precise same live Vec and emitted carrier/Result/frame; no borrowed contract substitution')
  row['named_hypotheses']=[dict(name='NEO::geometry_for_query.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
'''+marker)
s=s.replace("sorted(PEER_ROWS|set(parsers)|set(qrows)|set(orows))","sorted(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows))").replace("len(PEER_ROWS|set(parsers)|set(qrows)|set(orows))","len(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows))")
s=s.replace("delta['total_closed']==116 and delta['q_closed']==94", "delta['total_closed']==118 and delta['q_closed']==96")
p.write_text(s)
sys.path.insert(0,str(E));import NEO_validate as v,NEO_getter_certificates as g
e=v.obj(E/'NEO_EDGES.json');e['NEO_getter_row_certificates']=g.expected(v.baseline(),v.nen.q.check_receipt);(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(116,94,115)','(118,96,115)')
s=s.replace(' def mutate_parser(self,change):',''' def test_getter_same_live_carrier(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_getter_row_certificates'].values()))['domain']='Unrelated copied rows'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_getter_no_borrowed_substitution(self):
  e=copy.deepcopy(self.edges);next(iter(e['NEO_getter_row_certificates'].values()))['native_pair'][0]='NDI_K016'
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def mutate_parser(self,change):''');p.write_text(s)
