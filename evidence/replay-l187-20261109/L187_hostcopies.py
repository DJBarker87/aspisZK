import hashlib,json,sys
q=json.load(sys.stdin); rels=set(q['rels'])
res=dict(overlay={p:hashlib.sha256(open(p,'rb').read()).hexdigest() for p in q['overlays']},copies=[])
for line in open('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/all_oleans.txt'):
  p=line.rstrip('\n'); i=p.find('/',1)
  if any(p.endswith('/'+r) for r in rels):
    try: res['copies'].append((hashlib.sha256(open(p,'rb').read()).hexdigest(),p))
    except Exception: pass
print(json.dumps(res))
