from pathlib import Path
import json,sys
import NET_validate as v
import NET_window_certificates as w
import NET_wide_certificates as wd
import NET_peer_certificates as peer
import NET_prefix_certificates as pf
E=Path(__file__).resolve().parent
base=v.neo.baseline();old=v.obj(v.O/'NEO_EDGES.json');rows,edges=w.expected(base);r,e=wd.expected(base);rows+=r;edges.update(e)
r,e=pf.expected(base);rows+=r;edges.update(e)
pr,recipes,pe=peer.expected(base)
for edge in old['edges']:
 if edge['edge'] in pe:edge.update(pe[edge['edge']])
 elif edge['edge'] in edges:edge.update(edges[edge['edge']])
(E/'NET_CERTIFICATES.json').write_text(json.dumps(rows,indent=1)+'\n');(E/'NET_EDGES.json').write_text(json.dumps(old,indent=1)+'\n')
