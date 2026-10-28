"""Apply original-source codegen/inspection adjudications to the retained census."""
from pathlib import Path
import json,collections,hashlib,re
E=Path(__file__).resolve().parent;D=E/'diagnostics/d347';s=json.loads((E/'scan.json').read_text());inp=json.loads((E/'d347-input.json').read_text());plans=json.loads((E/'d347-plans.json').read_text());graphs={};candidates={}
for directory in sorted(D.glob('D*')):
 p=directory/'goto-scan.json'
 if not p.exists():continue
 for h in json.loads(p.read_text()):
  for original in inp['passes']:
   if original['harness']==h['harness'] and (directory.name=='D001' or original['index'] in plans[directory.name].get('indices',[])):
    graphs[original['index']]=(directory.name,h)
    candidates.setdefault((original['index'],directory.name),[]).append(h)
assert len(graphs)==len(inp['passes']),[(p['index'],p['harness']) for p in inp['passes'] if p['index'] not in graphs]
reasons={
 48:('EXEMPT',False,False,'call-name overapproximation','Excluded allocator diagnostic: all builtin paths are allocator growth/shrink helpers. Fixed reserve-from-empty/len=capacity shapes copy no pre-existing nonempty storage; no native link is restored.'),
 49:('EXEMPT',False,False,'call-name overapproximation','Excluded allocator-dispatch diagnostic. uninit reserves one element from empty; growth has no old allocation to copy. Generic allocator copy names overapproximate this fixed shape; diagnostic remains excluded.'),
 90:('EXEMPT',False,False,'rejects before the copy on the admitted domain','Both node_count calls receive an empty slice and return None at the initial length guard, before copying indices. Graph includes the nonempty callee branch, which is inadmissible here.'),
 153:('PROPERTY_INDEPENDENT',True,False,None,'paired_vectors reaches payload Vec clone/copy, but op34_exact_word asserts only is_empty(v) == (v.len()==0). Copied payload contents are not inputs to either boolean. No content-preservation law is inferred.'),
 156:('EXEMPT',False,False,'rejects before the copy on the admitted domain','n<=2 QM31 pushes fit the initial Vec capacity (at least4); no existing buffer is grown. try_into<[QM31;1024]> rejects at the length check and returns the original Vec before the array-copy branch. Both compared vectors were built by scalar pushes.'),
 158:('EXEMPT',False,False,'call-name overapproximation','pop_error_single pushes at most one Err(Error) into an empty Vec, then pops it. Initial allocation has no old buffer; no subsequent growth, clone or element-copy branch is admitted. Graph copy paths are generic allocator helpers. This is only the error/optional-singleton scope.'),
 196:('EXEMPT',False,False,'rejects before the copy on the admitted domain','The original factory guard receives the all-zero nonce and returns Error before OS randomness, the split copies and later successful construction. Original run01 lib and its libc0.2.191 dependency cohort are used; later factory manifests do not substitute for that PASS.'),
 213:('PROPERTY_INDEPENDENT',True,False,None,'Both halves are copied, but the assertion equates entropy_nonzero32 with != [0;32] on those same copied buffers. It asserts no preservation of the arbitrary original a bytes, as with acceptance_exact in the first audit.'),
}
def verdict(i,h):
 if not h['copy_paths']:return ('NO_REACHED_COPY',False,False,None,'No memcpy/memmove builtin is reachable from this exact metadata harness root in the lowered goto call graph; original source and compiler/configuration bindings are retained.')
 if i in reasons:return reasons[i]
 if i in [0,1,3,4]:why='node_count reaches its nonempty index copy (tail harness fixes one live index; count harness admits nonempty indices). The count/rejection location and, for tail, frame/callback assertions depend on that copied index storage. A malformed-padding rejection occurs after node_count, so it is not a before-copy exemption.'
 elif i==64:why='A feasible pivot with p != c reaches slice::swap -> ptr::swap -> memcpy/memmove on a three-u32 row. The nonzero selected-pivot assertion reads the swapped result; the control-only obligation was already OPEN.'
 elif i==101:why='Successful canonical 32-byte inputs reach WideExact::to_le_bytes -> copy_from_slice -> memcpy; bytes_success compares its result with the original arbitrary b. This source-predicate PASS has copy-dependent serializer support, without closing the already-open L2 rows.'
 elif i==151:why='Unrestricted-carrier all_carriers calls the shipped WideExact::to_le_bytes and compares its 32 output bytes with the owned serializer reference. The reconstructed native file SHA256 exactly matches the original receipt (frozen prefix plus committed original harness); its serializer copy is reached and observed.'
 elif i==263:why='padding_events_coordinate reaches digest_pad/callback 64-byte copies. The event-byte coordinate assertion observes those results. The owner already suspended this PASS5; its padding/finalize proposals concern already-OPEN V234/V235.'
 elif 197<=i<=204 or 218<=i<=230:why='The exact native source_root harness reaches memcpy in its selected source hashing/root construction. Native-versus-reference root assertions observe the copied data. Source/reference equations retain their stated scope, but this native association PASS is unavailable under ruling(r).'
 elif i in [209,211,212,214,215,217]:why='The original pv6 harness executes nonzero 32-byte copy_from_slice operations. Its value, frame, half-independence or zero-half assertion reads the copied destination and relies on preservation of the source bytes. These historical RunJoin native links are exposed, not new closed-row decrements.'
 else:raise AssertionError(('unreviewed copy root',i,h['harness']))
 return ('EXPOSED',True,True,None,why)
review=[]
for original in inp['passes']:
 i=original['index'];p=s['passes'][i];assert (p['harness'],p['pass_output_blob'])==(original['harness'],original['pass_output_blob']);run,h=graphs[i];status,reached,depends,exemption,why=verdict(i,h)
 diagnostic=dict(run=run,harness=h['harness'],metadata_and_paths=f'diagnostics/d347/{run}/goto-scan.json',graph=f'diagnostics/d347/{run}/'+h['graph_file'],goto_sha256=h['goto_sha256'],graph_sha256=h['graph_sha256'],bound=h['metadata']['attributes']['unwind_value'],source_binding='d347-source-bindings.json; d347-plans.json; original receipt/blob retained on this observation',candidate_goto_sha256s=sorted({c['goto_sha256'] for c in candidates[(i,run)]}),candidate_consistency='All matching metadata-root candidates in this scope have the same copy-path presence; all inventories retained, never a name-only clearance',identity_scope='Original receipt source hashes or committed original per-run snapshots; original surviving goto artifacts in D001; no solver or native-credit restoration')
 assert all(bool(c['copy_paths'])==bool(h['copy_paths']) for c in candidates[(i,run)]),(i,run,'candidate disagreement')
 p.update(status=status,copy_builtin_reached=reached,property_depends_on_copy=depends,exemption=exemption,reason=why,diagnostic=diagnostic)
 review.append(dict(index=i,harness=p['harness'],status=status,copy_builtin_reached=reached,property_depends_on_copy=depends,exemption=exemption,reason=why,**{'diagnostic':diagnostic}))
s['task']='LOG D346 / RESUME LOG D347';s['schema']='StreamB-K1-exposure-v2';s['coverage']='All 264 indexed historical PASS observations have reached-call inventory and admitted-domain/property adjudication; zero unresolved. This is a K-1 copy-exposure audit, not solver replay, universal tool fidelity, full native/deployment refinement or closure credit restoration.';s['counts']=dict(collections.Counter(p['status'] for p in s['passes']));s['exposed']=[i for i,p in enumerate(s['passes']) if p['status']=='EXPOSED'];s['unresolved']=[]
s['historical_support_rows_to_reverify_if_reused']=sorted({r for i in s['exposed'] for r in s['passes'][i]['ledger_rows']})
updates={
 'V185':'STANDS at the original scoped length-only property. D038 recovers exact op34_exact_word: payload copies are reached, but is_empty and the reference observe only len; no content native link is inferred.',
 'V186':'STANDS at the original default length/capacity scope. D038 recovers exact op35_exact_word with no reached copy builtin. No broader allocator/compiler/deployment closure is inferred.',
 'V187':'STANDS at prior scope. D039 recovers op36_reject_small: n<=2 fits the initial capacity and conversion rejects before its 1024-element copy. This preserves only the small rejection gate, not a successful-array conversion proof.',
 'V195':'SUSPENDED: both wide_flat and exact-source all_carriers (D037) reach serializer memcpy and compare its result. Raw.wide_bytes_flat is an owned reference, not an independently proved native serializer association.',
 'V184':'STANDS on the existing PV_AL_MoveClosure.complete / MoveWorld.source_reference and reference_memory structural route (STRUCTURAL-POP-GATE.json). The historical clone-based length0-4 gate remains suspended; D040 only preserves the optional-singleton Err(Error) gate by excluding growth. It does not replace the arbitrary-payload structural proof or establish compiler/deployment refinement.',
 'V234':'STANDS as already OPEN: recovered padding PASS5 (D001) is copy-exposed and cannot close or bridge padding/finalize. No adopted closure is decremented.',
 'V235':'STANDS as already OPEN: recovered padding PASS5 (D001) is copy-exposed and cannot close or bridge padding/finalize. No adopted closure is decremented.',
}
for row in s['row_consequences']:
 row['reason']=row['reason'].split(' Completed reached-call review marks supporting PASS observations ')[0]
 if row['row'] in updates:row['reason']=updates[row['row']]
 exposed=[i for i in row['supporting_passes'] if i in s['exposed']];row['exposed_supporting_passes']=exposed;row['unresolved_supporting_passes']=[]
 if exposed and row['consequence']=='STANDS' and row['row'] not in ['V177','V180','V184','V185','V186','V187','V234','V235']:
  row['reason']+=' Completed reached-call review marks supporting PASS observations '+', '.join(map(str,exposed))+' unavailable under K-1. This preserves the existing row scope only; those PASS observations supply no native association or new closure.'
scopes=[]
for directory in sorted(D.glob('D*')):
 f=directory/'scope.json'
 if not f.exists():continue
 r=json.loads(f.read_text());t=(directory/'time.log').read_text() if (directory/'time.log').exists() else '';cg=directory/'codegen.json'
 scopes.append(dict(run=directory.name,**r,peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1]) if re.search(r'Maximum resident set size \(kbytes\): (\d+)',t) else None,swaps=int(re.search(r'Swaps: (\d+)',t)[1]) if re.search(r'Swaps: (\d+)',t) else None,codegen=json.loads(cg.read_text()) if cg.exists() else None,original_pass_indices=plans[directory.name].get('indices',[]),target_source_revisions=sorted({p['source_revision'] for p in inp['passes'] if p['index'] in plans[directory.name].get('indices',[])},key=str)))
assert len(scopes)<=120
s['resume_budget']=dict(scope_limit=120,scopes_used=len(scopes),codegen_invocations=sum(x['codegen'] is not None for x in scopes),verification_runs=0,lean_attempts=0,receipt='d347-execution.json',notes='Includes setup failures, corrected source/flags reconstructions and inspection-only scopes. No solver verification invocation; no Lean or ELF/native build. Earlier D346 invocation budget retained separately.')
s['completed_audit']='d347-adjudications.json';(E/'scan.json').write_text(json.dumps(s,indent=2)+'\n');(E/'d347-adjudications.json').write_text(json.dumps(review,indent=2)+'\n');(E/'d347-execution.json').write_text(json.dumps(scopes,indent=2)+'\n')
(E/'ROWS.md').write_text('# Final K-1 row consequences (LOG D347)\n\nSTANDS preserves the prior status and exact scope; it does not close an OPEN/REDUCED row. Every indexed PASS is adjudicated.\n\n| Row | Prior status | Consequence | Reason |\n|---|---|---|---|\n'+''.join('| '+r['row']+' | '+str(r['before'])+' | **'+r['consequence']+'** | '+r['reason'].replace('|','/')+' |\n' for r in s['row_consequences']))
print(s['counts'],'scopes',len(scopes),'suspended',s['suspended_rows'])
