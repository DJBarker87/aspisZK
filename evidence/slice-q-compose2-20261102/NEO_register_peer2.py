from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;rev=json.loads((E/'NEO_NEI_PROVENANCE.json').read_text())['revision'];peer=json.loads((E/'NEO_PEER_POSITIVE.json').read_text())
p=E/'NEO_validate.py';s=p.read_text();lines=s.splitlines();lines=[('PEER_REV='+repr(rev)) if l.startswith('PEER_REV=') else ('PEER_ROWS='+repr(set(peer['delta']['composed_rows_closed']))) if l.startswith('PEER_ROWS=') else l for l in lines];s='\n'.join(lines)+'\n'
s=s.replace("len(packet['edges'])==4 and packet['delta']['edge_closed']==4","len(packet['edges'])==8 and packet['delta']['edge_closed']==8")
s=s.replace("packets=json.loads(data['evidence/slice-q-mul2-20261101/NEI_CTOR_PACKETS.json'])", "packets=json.loads(data['evidence/slice-q-mul2-20261101/NEI_CTOR_PACKETS.json'])+json.loads(data['evidence/slice-q-mul2-20261101/NEI_DOT_FINISH_PACKETS.json'])")
s=s.replace("packets += [json.loads(data[prefix+f]) for f in ['NEI_ROW_PACKET.json','NEI_PUSH_PACKET.json','NEI_WIDE_CTOR_PACKET.json']]", "packets += [json.loads(data[prefix+f]) for f in ['NEI_ROW_PACKET.json','NEI_PUSH_PACKET.json','NEI_WIDE_CTOR_PACKET.json']]\n packets += json.loads(data[prefix+'NEI_DOT_FINISH_PACKETS.json'])")
s=s.replace("  row=index[key];require(row['composed_status']=='OPEN','private-Q row collision')", "  if key in PEER_ROWS:\n   require(index[key]['function']==cert['function'],'overlapping peer/private-Q function differs')\n   index[key]['NEO_alternative_Q_certificate']=cert\n   continue\n  row=index[key];require(row['composed_status']=='OPEN','private-Q row collision')")
s=s.replace("delta['total_closed']==122 and delta['q_closed']==100 and delta['edge_closed']==118", "delta['total_closed']==128 and delta['q_closed']==106 and delta['edge_closed']==122")
p.write_text(s)
e=json.loads((E/'NEO_EDGES.json').read_text());updates={e['edge']:e for e in peer['edges']};e['edges']=[updates.get(item['edge'],item) for item in e['edges']];e['NEO_peer_row_certificates']=peer['row_certificates'];(E/'NEO_EDGES.json').write_text(json.dumps(e,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(122,100,118)','(128,106,122)');p.write_text(s)
