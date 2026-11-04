"""Additive NGB overlay application and reviewed delta composition. No proof launch."""
from pathlib import Path
import ast,json,lzma,hashlib,copy,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def J(p):
 p=R/p
 if p.exists():return json.loads(p.read_text())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert sha(raw)==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20000000:(E/(n+'.xz')).write_bytes(lzma.compress(raw));(E/(n+'.sha256')).write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
def closure(g,roots):
 seen={f:[f] for f in roots};q=collections.deque(roots)
 while q:
  f=q.popleft()
  for c in sorted(g[f]):
   if c in g and c not in seen:seen[c]=seen[f]+[c];q.append(c)
 return seen

def inventory():
 base=J('evidence/ledger7-20261104/NFX_LEDGER.json');overlay=J('evidence/inv-repair-20261104/NGB_OVERLAY.json')
 # Run the unchanged NGB apply function; its source pin is retained in overlay.
 p=R/overlay['producer']['path'];assert sha(p.read_bytes())==overlay['producer']['sha256']
 tree=ast.parse(p.read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='apply');ns=dict(sha=sha,R=R,json=json,copy=copy,collections=collections)
 exec(compile(ast.Module(body=[node],type_ignores=[]),str(p),'exec'),ns)
 old=ns['apply'](base,overlay);assert old['rows']==J('evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json')['rows']
 mir=R/'evidence/inv-defects-20261104/LEAD_B007/aspis_statement.mir.xz';raw=lzma.decompress(mir.read_bytes());assert sha(mir.read_bytes())=='088be272223412063fd2f6328c8d0f58ebc14a6e274ec957117072e5bd164b72'
 lines=raw.decode().splitlines();start=next(i for i,l in enumerate(lines) if l.startswith('fn external_local_packed_raw('));end=next((i for i in range(start+1,len(lines)) if lines[i].startswith('fn ')),len(lines))
 matches=[(i,l.strip()) for i,l in enumerate(lines[start:end],start) if '::map::' in l and 'state_only_poseidon::extension_limbs' in l];assert len(matches)==1
 f='crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw';t='crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs'
 src=J('evidence/inv-repair-20261104/NGB_SOURCE_AST.json');d=next(x for x in src if x['function']==f);assert any(x['text']=='input.map(extension_limbs)' for x in d['calls'])
 assert any(r['row']=='TX1:310' and r['function']==t for r in old['rows'])
 m=dict(id='NFZ_C0032',caller=f,callee=t,mir_path=str(mir.relative_to(R)),mir_sha256=sha(mir.read_bytes()),mir_uncompressed_sha256=sha(raw),mir_line=matches[0][0]+1,mir_text=matches[0][1],source_check='AGREES',source_sites=[x for x in d['calls'] if x['expression']=='extension_limbs'],compiler_gate='LEAD_B007 exit0 deployed statement MIR; no code generation or new native credit')
 put('NGJ_C0032_MIR.json',dict(edges=[m]));edge=dict(**{'from':f,'to':t},kind='callback',evidence=dict(path=str((E/'NGJ_C0032_MIR.json').relative_to(R)),sha256=sha((E/'NGJ_C0032_MIR.json').read_bytes()),method='rustc-MIR',compiler_gate_passed=True,records=['NFZ_C0032']))
 put('NGJ_EDGES.json',[edge]);o=dict(schema_version=2,name='NGJ reviewed C0032 supplement to NGB',new_rows=[],edge_list=dict(path=str((E/'NGJ_EDGES.json').relative_to(R)),sha256=sha((E/'NGJ_EDGES.json').read_bytes())),no_status_promotion=True)
 put('NGJ_OVERLAY.json',o);out=ns['apply'](old,o);assert len(out['rows'])==599
 assert all(a['composed_status']==b['composed_status'] for a,b in zip(old['rows'],out['rows']))
 return out

def build():
 for n in ['NFX','NGB','NFT','NFU','NFY','NGE','NGF','NGI','NFV']:assert J('evidence/ledger8-20261105/NGJ_REPLAY_'+n+'.json')['exit_status']==0,n
 out=inventory();original=copy.deepcopy(out['rows']);by={r['row']:r for r in out['rows']};promoted={};deltas=[]
 for folder,pre in [('slice-s-retarget-20261104','NFY'),('slice-s-retarget2-20261104','NGE'),('slice-s-retarget3-20261104','NGF'),('slice-s-join-20261105','NGI')]:
  delta=J('evidence/'+folder+'/'+pre+'_LEDGER_DELTA.json');deltas.append(dict(provider=pre,path='evidence/'+folder+'/'+pre+'_LEDGER_DELTA.json',sha256=sha((R/'evidence'/folder/(pre+'_LEDGER_DELTA.json')).read_bytes())))
  for c in delta['promotions']:
   r=by[c['row']];assert c['function']==r['function'];assert c.get('frozen_body_sha256',r['frozen_body_sha256'])==r['frozen_body_sha256'];assert r['composed_status'] in ['QUALIFIED','CLOSED']
   r.update(composed_status='CLOSED',NGJ_provider=pre,NGJ_route=r.get('NFX_route') or '(y)',NGJ_certificate=c);promoted[r['row']]=pre
 for folder,pre in [('slice-d-field-20261104','NFT'),('slice-d-check-20261104','NFU')]:
  delta=J('evidence/'+folder+'/'+pre+'_LEDGER_DELTA.json');ledger=J('evidence/'+folder+'/'+pre+'_COMPOSED_LEDGER.json');certs=J('evidence/'+folder+'/'+pre+'_CERTIFICATES.json');cb={r['row']:r for r in ledger['rows']}
  for rid in delta['new_closed_rows']:
   r=by[rid];c=cb[rid];assert c['function']==r['function'] and c['frozen_body_sha256']==r['frozen_body_sha256'] and c['composed_status']=='CLOSED'
   graph=r['canonical_callees'];r.update(copy.deepcopy(c));r['canonical_callees']=graph;r.update(NGJ_provider=pre,NGJ_route='(y)',NGJ_certificate=certs[rid]);promoted[rid]=pre
 # Preserve selected-claim denial, rather than rejecting unrelated OPEN callees.
 changed=True
 while changed:
  changed=False;denied={c for r in out['rows'] if r['composed_status']!='CLOSED' for c in r.get('selected_claims',[])};accepted={c for r in out['rows'] if r['composed_status']=='CLOSED' for c in r.get('selected_claims',[])}
  for r in out['rows']:
   bad=[c for o in r.get('caller_domain_obligations',[]) for c in o.get('callee_claims',[]) if c in denied and c not in accepted]
   if r['composed_status']=='CLOSED' and bad:r.update(composed_status='QUALIFIED',NGJ_denial=bad);changed=True
 for r in out['rows']:
  r.setdefault('NGJ_provider',r.get('NFX_provider','NGB OPEN'));r.setdefault('NGJ_route',r.get('NFX_route') if r['composed_status']=='CLOSED' else None)
  r['NGJ_trust_used']=sorted(set(r.get('NFX_trust_rows',[]))|({'NativeContractSemanticTransport'} if r['composed_status']=='CLOSED' else set()))
 graph=collections.defaultdict(set)
 for r in out['rows']:graph[r['function']].update(r['canonical_callees'])
 spec=J('docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices'];root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
 sets={s:set(closure(graph,spec[s]['roots'])) for s in ['Q','S']};sets['D']=set(closure(graph,[root]))-sets['Q']-sets['S']
 def counts(rs):return dict(total=len(rs),**{s:sum(r['composed_status']==s for r in rs) for s in ['CLOSED','QUALIFIED','OPEN']})
 slices={}
 for s in ['S','Q','D']:
  rr=[r for r in out['rows'] if r['function'] in sets[s]];roots=[]
  for f in spec[s]['roots'] if s!='D' else [root]:
   rows=[r for r in rr if r['function']==f];roots.append(dict(function=f,rows=[r['row'] for r in rows],status='CLOSED' if all(r['composed_status']=='CLOSED' for r in rows) else 'QUALIFIED' if any(r['composed_status']=='QUALIFIED' for r in rows) else 'OPEN'))
  slices[s]=dict(**counts(rr),roots=roots,roots_CLOSED=sum(r['status']=='CLOSED' for r in roots),functions=len(sets[s]))
 routes={r['row']:dict(function=r['function'],status=r['composed_status'],route=r['NGJ_route'],provider=r['NGJ_provider'],trust_used=r['NGJ_trust_used']) for r in out['rows']}
 trust=copy.deepcopy(out['trust_rows'])
 for t in trust:t['direct_closed_rows']=[r['row'] for r in out['rows'] if r['composed_status']=='CLOSED' and t['id'] in r['NGJ_trust_used']]
 out.update(NGJ_headline='AspisR1.RPx_Deployed.deployed',NGJ_coverage=counts(out['rows']),NGJ_per_tx={tx:counts([r for r in out['rows'] if r['transaction']==tx]) for tx in ['TX1','TX2']},NGJ_slices=slices,NGJ_security_target_established=False,NGJ_cold_release_replay=False,NGJ_promoted=promoted,NGJ_source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),NGJ_authority='NGJ fields and composed_status; other checkpoint fields retained history')
 put('NGJ_LEDGER.json',out);put('NGJ_ROUTES.json',routes);put('NGJ_TRUST_USED.json',dict(rows=trust,additional_reviewed_transcription_ah_uses=[],Pool_A='(af) std/allocator reclassification; no verifier inventory row',no_trust_removed=True));put('NGJ_SLICES.json',{s:sorted(fs) for s,fs in sets.items()})
 lines=['# Ledger refresh 8','','Target not yet established. CLOSED denotes conditional hybrid composition under the accepted trust inventory. The full Pool-plus-verifier import FAILED; the independently coherent verifier closure is audited separately.','','| Scope | Total | CLOSED | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|']
 for s,v in [('all',out['NGJ_coverage']),*out['NGJ_per_tx'].items(),*slices.items()]:lines.append('| '+s+' | '+' | '.join(str(v[k]) for k in ['total','CLOSED','QUALIFIED','OPEN'])+' |')
 lines+=['','599-row NGB basis; C0032 adds one reviewed callback edge through the unchanged NGB apply producer, no row or slice membership change. NFT and NFU both close TX1:342, counted once. The D expected 47 is checked against actual set union, not assumed. Pool has zero consumer rows in this verifier inventory and remains OPEN.','', 'Routes preserve (y), (ad), (ae), source reclassification; no (ah) row is supplied by this checkpoint. Pool A uses (af) reclassification outside the verifier inventory. Native-contract transport is reclassification, never removal. RuntimeReturnData (nonempty 1..1024, ASR8 792) and RuntimeMemcmp are ACCEPTED. L154 is a statement parameter; digest/error are op43/op44.','', '| Row | Function | Status | Route | Provider |','|---|---|---|---|---|']
 lines += ['| '+r['row']+' | '+r['function']+' | '+r['composed_status']+' | '+str(r['NGJ_route'] or '')+' | '+r['NGJ_provider']+' |' for r in out['rows']]
 (E/'NGJ_LEDGER.md').write_text('\n'.join(lines)+'\n');print(json.dumps(dict(coverage=out['NGJ_coverage'],slices=slices)))
if __name__=='__main__':build()
