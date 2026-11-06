"""Complete statement/domain comparison, including archived caller clauses."""
from pathlib import Path
import json,lzma,hashlib,copy,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger22-20261110';Q=E.parent/'terminal6-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(b));Path(str(p)[:-3]+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
statements={}
for line in raw(E/'NLS_L002/stdout.log').decode().splitlines():
 if 'NLS_OWNER 'in line:
  x=json.loads(line.split('NLS_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NLO_KERNEL_STATEMENTS.json.xz');assert all(statements.get(n)==v for n,v in old.items())
assert set(statements)==set(J(E/'NLS_AUDIT_ROOTS.json')['roots'])
put('NLS_KERNEL_STATEMENTS.json.xz',statements);put('NLS_OWNER_COMPARISON.json',dict(status='PASS',previous=len(old),identical=len(old),new=len(statements)-len(old),wrong=[]))
b=J(P/'NLO_LEDGER.json.xz');by={r['row']:r for r in b['rows']};cs=J(Q/'NLH_CLOSED.json')['functions'];ids={c['row']for c in cs};occ=J(Q/'NLH_CALLEE_COMPOSITION.json')['rows']
common=[('hd','NKR_DigestChildren.Domain pub'),('hc','canonical claims'),('hp','canonical point'),('hl','Canon lambda'),('hchi','Canon chi'),('ht','Canon theta'),('asset','pub.asset_id.val < 2147483647')]
domains={
'TX1:261':[('hd','NKR_DigestChildren.Domain pub'),('hz','canonical o.z'),('hs','canonical o.succ_z'),('hx','canonical o.xor12_z'),('hh','canonical s.high'),('hl','canonical s.low'),('asset','pub.asset_id.val < 2147483647'),('amount','(core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val < 2147483647')],
'TX1:237':common,
'TX1:263':common+[('hz','canonical zc'),('hm','Canon mu')],
'TX1:256':[('hd','NKR_DigestChildren.Domain (NKR_TermPublic.value pub)'),('hc','∀ row∈claims.val,canonical row'),('hp','canonical point'),('hz','canonical c.zc'),('hl','Canon c.lambda'),('hchi','Canon c.chi'),('ht','Canon c.theta'),('hm','Canon c.mu'),('asset','(NKR_TermPublic.value pub).asset_id.val < 2147483647')]}
reviews={
'TX1:261':'ONE21-event fold. SemanticPrefix starts packed24 at zero; source packet supplies exact canonical consecutive232/229/233/228 results at unchanged Public/openings/selectors. NKR_DigestRoot/Wrapper supplies CLOSED250 two-cell result, not free replies; TermDigestFrame transports packed values. ScalarInvocation establishes all12 field operand domains and92 preweighted tail from asset/amount and actual arrays. Canonical full packed24, complete source/cohort Result, order and attempted prefix are conclusions. Native windows associate full pre/post state under reviewed option-A transport.',
'TX1:237':'ONE parent state, amount/validation then4gathers/selectors/308/261/H1/variant/218/prepared/28Horner/G. CompRoot handles InvalidPublicAmount and every validation Err/fail/div without suffix; TermAmount.canonical derives261 amount bound at actual pub amount. GatherPoseidon constructs canonical z/succ/xor/high/low, block/local16 and DETERMINISTIC CLOSED308 call at those arguments. CompCopy uses actual z/H1/selectors/lambda/chi/next_pair_index/copy_variant and NKR218 native-to-cohort law; inherited primitive registry metadata/lookup cut transcription stays explicit P6 trust. Prepared theta/domain, accumulator/canonical remaining and length28 are derived internally. Full six channels and attempted prefix on every Result are retained.',
'TX1:263':'Applies237 internally at identical pub/claims/point/lambda/chi/theta and identical own-input predicates. Every fail/div/Err is mapped with no arithmetic suffix; on Ok all six channels retained and NKR_TermTail.result derives suffix canonical operands for SAME zc/point/mu. ONE nine-event arithmetic suffix; full four-channel Result/order/frame is concluded.',
'TX1:256':'WrapperGathers proves84 actual selected cells with full logical array frame and canonicality from every own claims row; SAME255 public projection is NKR_TermPublic.value pub. PartsRoot applies263 at exactly gathered84,point,c.lambda/chi/theta/zc/mu. All domains discharged from own predicates; both Rust map/map_err arms plus outer fail/div are retained. Result is native/source/cohort four-channel projection to scalar; caller136 must establish every own-argument clause, never global success.'}
rows=[];parents=[];matrix=[];sources=[]
for c in cs:
 rid=c['row'];r=by[rid];assert r['status']=='OPEN'and r['function']==c['function']and r['frozen_body_sha256']==c['frozen_body_sha256']
 file,name=r['function'].split('::',1);fn=name.split('::')[-1];text=subprocess.check_output(['git','show',c['frozen_revision']+':'+file]).decode()if 'frozen_revision'in c else subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+file]).decode()
 start=re.search(r'fn '+re.escape(fn)+r'(?:<|\()',text).start();a=text.index('{',start);z=a+1;d=1
 while d:d+=(text[z]=='{')-(text[z]=='}');z+=1
 assert H(text[a:z].encode())==r['frozen_body_sha256']
 source=raw(Q/(c['module']+'.lean'));rc=J(Q/c['receipt']);assert rc['exit_status']==0 and H(source)==c['source_sha256']==rc['source_hashes'][c['module']+'.lean']
 root=statements[c['root']];assert root['owner_module']==c['module']
 domain=[dict(name=n,verbatim=v,classification='bf(2) own-input canonicality/range/projection/provenance')for n,v in domains[rid]]
 # Every binder is present in the source statement, not inferred from the theorem name.
 block=source.decode().split('theorem source',1)[1].split(' := by',1)[0]
 for clause in domain:assert re.sub(r'\s+','',clause['verbatim'])in re.sub(r'\s+','',block),clause
 original=copy.deepcopy(r['obligation'])
 def walk(x,path='obligation'):
  if isinstance(x,dict):
   if any(k in x for k in ['required','domain','required_named_hypotheses'])or ('status'in x and any(k in x for k in ['callee','caller_clause','helper'])):
    matrix.append(dict(row=rid,path=path,original=x,disposition=reviews[rid],classification='Historical statement preserved; source/helper law discharged internally at same actual arguments. Enclosing argument provenance remains an explicit bf caller clause.',effective_status='INTERNAL_DISCHARGED_FOR_THIS_ROW'))
   for k,v in x.items():walk(v,path+'.'+k)
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,path+'['+str(i)+']')
 walk(original)
 own_occ=[x for x in occ if x['parent']==rid]
 assert set(c['children'])=={x['child']for x in own_occ}
 for x in own_occ:assert by[x['child']]['status']=='CLOSED'or x['child']in ids
 rows.append(dict(row=rid,provider='NLH',function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],certificate=c,roots=[c['root']],primary_root=c['root'],kernel_statements=[root],root_domain=domain,hypothesis_inventory=[dict(clause=v,inventory='bf(2)',forbidden_conclusion_premise=False)for v in domain],original_clauses=original,review=reviews[rid],callee_occurrences=own_occ,recommendation='ADMIT_ONLY_AFTER_GATE',gate_admitted=False))
 # Every canonical caller retains verbatim predicates, even an OPEN caller.
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  match=[x for x in occ if x['parent']==par['row']and x['child']==rid]
  if par['row']in ids:assert match
  for clause in domain:
   parents.append(dict(parent=par['row'],helper=rid,occurrences=match or ['Canonical caller occurrence; actual argument provenance remains OPEN'],caller_clause=dict(id=f'NLS-bf:{par["row"]}:{rid}:{clause["name"]}',caller=par['function'],callee=r['function'],required=clause['verbatim'],name=clause['name'],classification=clause['classification'],status='INTERNAL_DISCHARGED'if par['row']in ids else'OPEN',discharged_by=match[0]['domain_installation']if match else None,reason='Exact own-input clause retained at every actual caller. Source binder names are instantiated by the named SAME-argument occurrence. No parent promotion.')))
# Carry the inherited semantic-eval lineage context to each new helper's parent too.
for c in cs:
 rid=c['row'];r=by[rid]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  match=[x for x in occ if x['parent']==par['row']and x['child']==rid]
  for context in r['obligation']['inventory_domain_obligations']:
   parents.append(dict(parent=par['row'],helper=rid,kind='inventory:'+context['unit'],occurrences=match or ['Actual native/source argument lineage at caller remains OPEN'],caller_clause=dict(id=f'NLS-context:{par["row"]}:{rid}:{context["unit"]}',caller=par['function'],callee=r['function'],required=context['domain'],classification='Retained original inventory argument provenance; not an extra root output/success premise',status='INTERNAL_DISCHARGED'if par['row']in ids else'OPEN',discharged_by=match[0]['domain_installation']if match else None,reason='Original unit/provenance context preserved alongside verbatim bf own-input domains.')))
# Also discharge inherited child-domain occurrence clauses already recorded by predecessor ledgers.
child_reviews=[]
for x in occ:
 par=by[x['parent']];child=by[x['child']];found=[]
 def clauses(v,path='obligation'):
  if isinstance(v,dict):
   if v.get('callee')==child['function']and('required'in v or 'status'in v):found.append(dict(path=path,clause=v))
   if v.get('helper')==child['row']and'caller_clause'in v:found.append(dict(path=path,clause=v['caller_clause']))
   for k,w in v.items():clauses(w,path+'.'+k)
  elif isinstance(v,list):
   for i,w in enumerate(v):clauses(w,path+'['+str(i)+']')
 clauses(par['obligation'])
 child_reviews.append(dict(**x,inherited_caller_clauses=found,disposition='INTERNAL_DISCHARGED_AT_SAME_ARGUMENTS',review=reviews[x['parent']],child_basis_status=child['status'],child_basis_owner=child.get('owner_module'),child_basis_obligation=child['obligation_statement_hash']))
assert by['TX1:308']['status']=='CLOSED'
for m,a in J(Q/'NLH_GATE_SOURCES.json')['passed'].items():
 p=Q/(m+'.lean');rc=J(Q/a/'receipt.json');assert rc['exit_status']==0 and H(raw(p))==rc['source_hashes'][p.name]
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s',raw(p).decode(),re.M)
 sources.append(dict(module=m,path=str(p),sha256=H(raw(p)),receipt=str(Q/a/'receipt.json')))
combined=(Q/'NLH_COMBINED_IMPORT.lean').read_text();assert all(not l.strip()or l.startswith('import ')or l=='#print axioms AspisR1.RPx_Deployed.deployed'for l in combined.splitlines())
generator=(Q/'NLH_build_gate.py').read_text();assert "text=''.join('import '+m+'\\n'"in generator and "gate_generator_private_source_checks=False"in generator
put('NLS_CANDIDATE_REVIEW.json',dict(status='SEMANTIC_REVIEW_GATE_PENDING',rows=rows,admissible=4,rejected=0));put('NLS_PARENT_CLAUSES.json',dict(clauses=parents,parents=sorted({v['parent']for v in parents}),support=[]));put('NLS_CLAUSE_MATRIX.json.xz',dict(status='PASS_COMPLETE_CLAUSE_REVIEW',clauses=matrix,original_count=len(matrix),callee_occurrence_reviews=child_reviews,ruling='aq2/bf2/bf3',no_conclusion_hypotheses=True));put('NLS_SOURCE_OBJECT_REVIEW.json',dict(status='PASS_COMMITTED_SOURCE_HASHES_MATCH_SUCCESSFUL_COMPILES',sources=sources,combined_modules_only=True,generator_modules_only=True,private_raw_inventory_retained=True))
# Record all lead ruling headings through bf and pin the complete immutable ruling source.
p=Path('docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md');s=p.read_text();put('NLS_RULINGS.json',dict(path=str(p),sha256=H(p.read_bytes()),headings=[l for l in s.splitlines()if l.startswith('#')],latest_binding='bf',binding=['aq2','aq5','ax2','bd','be','bf'],scope='No ruling or trust item edited'))
print(json.dumps(dict(candidates=len(rows),recursive_clause_records=len(matrix),parent_clauses=len(parents),callee_occurrences=len(child_reviews),sources=len(sources),unchanged_roots=len(old))))
