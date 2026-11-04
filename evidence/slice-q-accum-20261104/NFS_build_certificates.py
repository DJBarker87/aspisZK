"""Additive four-part ruling-(y)/(ae) packets; no inherited ledger edits."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent;P=E.parent/'slice-q-values-20261104'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ref=lambda p:dict(path=str(p.relative_to(R)),sha256=sha(p))
rows={'TX1:089':'query_values','TX2:059':'query_values','TX1:088':'query_loop','TX2:058':'query_loop'}
base=json.loads((P/'NFP_CLOSED.json').read_text());native=json.loads((E/'NFS_NATIVE_REUSE.json').read_text())
trust=base['trust']+'; native/library interpretation remains explicit root P6/TrustedStd boundary; digest/error slots43/44'
common=dict(frozen_revision=native['frozen_source'],route='CLOSED under (ae)',trust=trust,residual_inner_hypotheses=[],root_physical_interpretation_retained=True,new_trust_items=[],security_target_established=False,cold_release_replay=False)
callee_packets=[ref(E.parent/'slice-q-mul9-20261104/NFM_CERTIFICATES.json'),ref(E.parent/'slice-q-mul3-20261103/NEV_ACCUM_PACKET.json'),ref(E.parent/'slice-q-compose6-20261104/NFG_EDGES.json')]
query=dict(id='NFS-query-values',function='crates/aspis-r1-cost-probe/src/candidate.rs::query_values',status='CLOSED under (ae)',**common)
query['domain']='NFS_PacketRoot.Domain on SAME proof57607, p, g29, geometry, accumulator and pending; active next<finish (finish10 or22); canonical input weights/rhs/power/rho/alphas and g, SAME-vector raw Progress, width64, local+TXstart=global next; geometry lengths finish-start and canonical selected cells. Input data only; Prepared/powers/prepare producer boundaries retained.'
query['four_parts']={
 'native':dict(revalidated=ref(E/'NFS_NATIVE_REUSE.json'),certificates='NFP_K007/009 prefix,012/014 suffix,016/018 owned-return frame,020/022 scalar node,025–035 geometry,060–076 readonly context projections; all matched failing/copy controls and13 rename families; exact deployed None route and frozen lock/features',contracts=[]),
 'emitted_child_models':dict(packets=callee_packets,retarget=ref(E/'NFS_RETARGET_PROVENANCE.json'),fold_retarget=ref(E/'NFS_FOLD_PROVENANCE.json'),theorems=['NFM_ProductInstance.installed/wrapper','NFS_NEV_AccumPacket.result_state_effects','NFS_NEV_AccumulateComplete.native','NFS_FoldInstall.line/circle/domains','NFS_NEI_LineBridge.complete','NFS_NEI_CircleBridge.complete'],field_stubs=ref(E/'LPh_STUBS.md')),
 'caller_domains_and_frames':dict(theorems=['NFS_CallerDomains.no_seed','NFS_CallerDomains.fields/dots/folds','NFS_PacketRoot.geometry/node','NFS_AccumDomain.line/domain','NFS_AccumInstall.installed','NFP_HeadDomain.reached','NFP_DotDomains.returned','NFP_FrameExt.raw','NFP_ReturnCuts.erased/continuation'],physical='Root ABI/heap/allocator/source-to-ELF interpretation retained; child call inputs, returned owned vectors, readonly context and exact frame are SAME native-cut objects, not independent successful executions'),
 'result_state_ordered_effects':dict(theorems=['NFS_DotTrace.head','NFS_TraceBack.installed','NFS_QueryValuesPacket.source/result','NFS_PacketRoot.query','NFP_RejectionTrace.rejected_prefix'],statement='Complete partial Result and M.cuts equality, including failures/divergence/rejection prefixes; returned accumulator/pending and readonly root context supplied by same native frame certificates')}
loop=dict(id='NFS-query-loop',function='crates/aspis-r1-cost-probe/src/candidate.rs::query_loop',status='CLOSED under (ae)',**common)
loop['domain']='SAME root domain; actual TX1 next0,finish10,fuel10 or TX2 next10,finish22,fuel12. Generic arbitrary-prestate helper includes Err/stopped/failure/divergence/child error and success. No successful child reply or independent invariant is an input.'
loop['four_parts']={
 'native':dict(revalidated=ref(E/'NFS_NATIVE_REUSE.json'),certificates='NFP_K036–058 exact frozen ONE iteration, arbitrary owned prestate and all8 Error variants; NFP_K060–076 exact readonly context tuple projections; paired failing/copy/rename controls',whole_loop_unwind=False),
 'emitted_child_models':dict(child='NFS-query-values',theorems=['NFG_QueryLoopSource.complete','NFP_LoopTerminals.error/stopped/rejected/failed/diverged','NFP_Resume.tx1/tx2']),
 'caller_domains_and_frames':dict(theorems=['NFS_QueryInvariant.active/step','NFS_QueryLoopRoot.finite/root/tx1/tx2','NFP_QueryAdvance.accepted/offset'],statement='Canonical rhs/power, same weight frame, raw Progress, independent local/global counter offset and active child domain are DERIVED from each earlier SAME returned child'),
 'result_state_ordered_effects':dict(theorems=['NFS_LoopTraceDefs.compare/erased','NFS_LoopTrace.source','NFS_PacketRoot.loop','NFS_QueryLoopRoot.tx1/tx2'],statement='Finite induction of complete partial Result and concatenated ordered M.cuts; exact source wrapper at actual TX1/TX2 budgets; root physical interpretation only')}
certs=[query,loop]
closed=dict(schema='NFS-NDT-four-part-v1',headline='AspisR1.RPx_Deployed.deployed',baseline=ref(P/'NFP_CLOSED.json'),newly_closed=list(rows),new_count=4,rows={r:dict(function=next(c['function'] for c in certs if c['function'].endswith('::'+f)),status='CLOSED under (ae)',certificate='NFS-'+f.replace('_','-')) for r,f in rows.items()},certificates=certs,root_status='CLOSED under (ae)',**{k:v for k,v in common.items() if k not in ['route']})
intake=json.loads((P/'NFP_EDGE_INTAKE.json').read_text());overrides=[]
pruned={r['edge']:r for r in native['typed_pruning']}
for r in intake:
 if r['status']!='OPEN':continue
 cert=pruned.get(r['edge'],dict(kind='DIRECT_CALL',domain=query['domain'] if r['caller'].endswith('query_values') else loop['domain'],parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],theorems=query['four_parts']['caller_domains_and_frames']['theorems']+query['four_parts']['result_state_ordered_effects']['theorems'] if r['caller'].endswith('query_values') else loop['four_parts']['caller_domains_and_frames']['theorems']+loop['four_parts']['result_state_ordered_effects']['theorems'],residual_inner_hypotheses=[]))
 overrides.append(dict(edge=r['edge'],status='CLOSED under (ae)',certificate=dict(id='NFS-edge:'+r['edge'],**cert)))
edges=dict(schema='NFS-additive-edges-v1',baseline=ref(P/'NFP_EDGES.json'),inventory_edge_count=257,inherited_closed=199,newly_closed=[r['edge'] for r in overrides],new_count=len(overrides),edge_closed=199+len(overrides),overrides=overrides,qualification='Conservative NFP/NFM baseline count only; NFN geometry retained separately without double-counting or refreshing the unified ledger')
delta=dict(schema='NFS-additive-NDT-v1',headline=closed['headline'],baseline=ref(P/'NFP_LEDGER_DELTA.json'),newly_closed=list(rows),new_count=4,rows={r:'CLOSED under (ae)' for r in rows},newly_certified_edges=edges['newly_closed'],new_edge_count=len(overrides),edge_total=257,edge_closed=edges['edge_closed'],query_values_incoming_edge_closed=True,route='CLOSED under (ae)',route_rows=list(rows),sibling_geometry_ref=ref(E.parent/'slice-q-phase-20261104/NFN_LEDGER_DELTA.json'),sibling_credit_double_counted=False,trust=trust,security_target_established=False,cold_release_replay=False)
for n,x in [('CLOSED',closed),('EDGES',edges),('LEDGER_DELTA',delta)]:
 (E/('NFS_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
