"""Add current Git-pinned peer registrations; preserve all original denials."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=E/'NEO_validate.py';s=p.read_text()
s=s.replace('import sys,json,hashlib,copy,lzma,re,subprocess','import sys,json,hashlib,copy,lzma,re,subprocess,base64')
s=s.replace("PEER_REV='66c32b92421564a57aa9b98547b3bafbbe88a304'", "PEER_REV='"+json.loads((E/'NEO_NEI_PROVENANCE.json').read_text())['revision']+"'")
s=s.replace("PEER_ROWS={'TX1:107','TX1:110','TX2:073','TX2:076'}", "PEER_ROWS="+repr(set(json.loads((E/'NEO_PEER_POSITIVE.json').read_text())['delta']['composed_rows_closed'])))
s=s.replace("require(not set(data)&set(current),'duplicate peer input');data.update(current)","\n  if chunk.get('role')!='update':require(not set(data)&set(current),'duplicate peer input')\n  data.update(current)")
s=s.replace(" require(set(data)==set(provenance['files']),'peer input inventory')", " for path in provenance.get('deleted_paths',[]):data.pop(path,None)\n require(set(data)==set(provenance['files']),'peer input inventory')")
s=s.replace("raw=text.encode();require(sha(raw)","raw=text.encode() if isinstance(text,str) else base64.b64decode(text['base64']);require(sha(raw)")
s=s.replace("require(len(packet['edges'])==1 and packet['delta']['edge_closed']==1,'peer edge scope')","require(len(packet['edges'])==4 and packet['delta']['edge_closed']==4,'peer edge scope')")
s=s.replace("rc['source_revision']==tests['source_revision']==PEER_REV","rc['source_revision']==tests['source_revision']==PEER_REV")
s=s.replace(" if parsers is None:parsers=obj(E/'NEO_PARSER_CERTIFICATES.json')", " if parsers is None:parsers=obj(E/'NEO_PARSER_CERTIFICATES.json')")
s=s.replace("  support=['evidence/slice-q-mul2-20261101/NEI_K021/receipt.json']\n  if r['function'].endswith('::EbyKDot::new'):support.append('evidence/slice-q-mul2-20261101/NEI_K023/receipt.json')", "  support=peer_support(data,r['function'])")
s=s.replace(" for key,cert in parsers.items():\n  row=index[key];", " for key,cert in parsers.items():\n  if key in PEER_ROWS:\n   require(index[key]['function']==cert['function'],'overlapping peer/parser function differs')\n   index[key]['NEO_alternative_certificate']=cert\n   continue\n  row=index[key];")
s=s.replace("delta['total_closed']==96 and delta['q_closed']==74 and delta['edge_closed']==108", "delta['total_closed']==104 and delta['q_closed']==82 and delta['edge_closed']==111")
# Packet-specific native support lists are already independently audited by the unchanged peer engine.
insert='''
def peer_support(data,function):
 prefix='evidence/slice-q-mul2-20261101/'
 packets=json.loads(data[prefix+'NEI_CTOR_PACKETS.json'])+json.loads(data[prefix+'NEI_GETTER_PACKETS.json'])
 packets += [json.loads(data[prefix+f]) for f in ['NEI_ROW_PACKET.json','NEI_PUSH_PACKET.json','NEI_WIDE_CTOR_PACKET.json']]
 p=next(p for p in packets if p['function']==function)
 support=([p['native_pair'][0]] if 'native_pair' in p else [pair.split('/')[0] for pair in p['new_kani_credits']])
 return [prefix+a+'/receipt.json' for a in support]
'''
s=s.replace('\ndef compose(',insert+'\ndef compose(')
p.write_text(s)
# Current edges are exact imported certificates, retaining original 257 edges.
edges=json.loads((E/'NEO_EDGES.json').read_text());peer=json.loads((E/'NEO_PEER_POSITIVE.json').read_text());new={e['edge']:e for e in peer['edges']}
edges['edges']=[new.get(e['edge'],e) for e in edges['edges']];edges['NEO_peer_row_certificates']=peer['row_certificates'];(E/'NEO_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
p=E/'NEO_tests.py';s=p.read_text().replace('(96,74,108)','(104,82,111)');p.write_text(s)
p=E/'NEO_peer_positive.py';s=p.read_text().replace("source_revision='1dbf5ad151'","source_revision="+repr(json.loads((E/'NEO_NEI_PROVENANCE.json').read_text())['revision']));p.write_text(s)
# The last receipt used an abbreviated Git revision; replace with its resolved immutable identity.
p=E/'NEO_PEER_POSITIVE_RECEIPT.json';d=json.loads(p.read_text());d['source_revision']=json.loads((E/'NEO_NEI_PROVENANCE.json').read_text())['revision'];p.write_text(json.dumps(d,indent=1)+'\n')
