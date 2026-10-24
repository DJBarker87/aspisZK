#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys,runpy
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
args=sys.argv[:];sys.argv=[str(R/'tools/s6-full-forest-roundtrip-20261023/generate-current-adapter-carrier.py'),'--check'];old=runpy.run_path(sys.argv[0]);sys.argv=args
parse=old['parse'];a=parse(S/'AdapterRwTypes.lean');v=parse(S/'CurrentCompactCallerTypesV1.lean')
qs=['aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1','aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1','aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1','aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1','aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1','aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public','aspis_r1_cost_probe.verifier.Error','aspis_r1_cost_probe.verifier.Phase']
c={q:a[q] for q in qs};native_name=lambda q:q.replace('aspis_r1_cost_probe.','')
norm=lambda s:re.sub(r'\s+','',s.replace('aspis_r1_cost_probe.',''))
for q,row in c.items():
 other=v[native_name(q)]
 assert row['kind']==other['kind'] and [x[0] for x in row['items']]==[x[0] for x in other['items']],q
 for (_,x),(_,y) in zip(row['items'],other['items']):assert norm(x)==norm(y),(q,x,y)
leaf=lambda q:q.split('.')[-1];CN='AdapterRw.';NN='AspisR1CurrentCaller.'
map_expr=lambda direction,ty,x:(direction+leaf(ty)+' ('+x+')') if ty in c else x
out='import AdapterRwTypes\nimport CurrentCompactFirstCompositionV1\nset_option autoImplicit false\nopen Aeneas Aeneas.Std\nnamespace AspisS6CurrentVerifierCarrier\n\n'
prior=[]
for q,row in c.items():
 name=leaf(q);nt=native_name(q)
 for direction,src,dst in [('to',CN+q,NN+nt),('from',NN+nt,CN+q)]:
  out+='def '+direction+name+' (value : '+src+') : '+dst+' :=\n'
  if row['kind']=='structure':out+='  {'+','.join(field+':='+map_expr(direction,ty,'value.'+field) for field,ty in row['items'])+'}\n\n'
  else:
   out+='  match value with\n'
   for ctor,sig in row['items']:
    parts=[s.strip() for s in sig.split('→')];assert parts[-1]==q
    params=['x'+str(i) for i in range(len(parts)-1)]
    out+='  | .'+ctor+(' '+' '.join(params) if params else '')+' => '+dst+'.'+ctor+(' '+' '.join('('+map_expr(direction,ty,x)+')' for ty,x in zip(parts[:-1],params)) if params else '')+'\n'
   out+='\n'
 for direction,src in [('from_to',CN+q),('to_from',NN+nt)]:
  expr='from'+name+' (to'+name+' value)' if direction=='from_to' else 'to'+name+' (from'+name+' value)'
  lemmas=','.join([direction+leaf(x) for x in prior])
  out+='@[simp] theorem '+direction+name+' (value : '+src+') : '+expr+'=value := by\n'
  out+='  cases value <;> simp only [to'+name+',from'+name+(','+lemmas if lemmas else '')+']\n  all_goals rfl\n\n'
 out+='def equiv'+name+' : '+CN+q+' ≃ '+NN+nt+' where\n  toFun := to'+name+'\n  invFun := from'+name+'\n  left_inv := from_to'+name+'\n  right_inv := to_from'+name+'\n\n#print axioms equiv'+name+'\n\n'
 prior.append(q)
out+='end AspisS6CurrentVerifierCarrier\n'

sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=dict(schema='focused-extractor-proof-packet-v1',adapter_types_sha256=sha(S/'AdapterRwTypes.lean'),verifier_types_sha256=sha(S/'CurrentCompactCallerTypesV1.lean'),complete_declarations=c,candidate_sha256=hashlib.sha256(out.encode()).hexdigest())
p=S/'S6CurrentVerifierCarrierV1.lean';m=E/'s6-current-verifier-carrier-generation.json'
if '--check' in sys.argv:assert p.read_text()==out and json.loads(m.read_text())==json.loads(json.dumps(meta))
else:p.write_text(out);m.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(full_declarations=len(c))))
