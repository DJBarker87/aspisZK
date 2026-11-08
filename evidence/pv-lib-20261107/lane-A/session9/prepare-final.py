"""Collect checked roots; preserve slot statuses and the strict walker unchanged."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path('evidence/pv-lib-20261107/lane-A/session9');A=E.parent;M=A.parent/'PLIB_MAP.json';base='a04fdc3582a'
sha=lambda b:hashlib.sha256(b).hexdigest()
support=[];roots=[];attempts=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());attempts.append({k:r[k]for k in ['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_sha256']})
 if not r['accepted']or r['runtime_audit']or'RawAudit'in r['target']:continue
 raw=Path(r['source_path']).read_bytes();assert sha(raw)==r['source_sha256'],r['target']
 names=[re.match(r"'([^']+)'",v)[1]for v in r['axioms_summary_based']]
 assert names and all('sorryAx'not in v for v in r['axioms_summary_based'])
 support.append(dict(module=r['target'],source=r['source_path'],source_sha256=r['source_sha256'],attempt=r['attempt'],roots=names,qualification='Checked local source/metadata/allocator-lifetime support; full last-strong/callback/caller-history adequacy remains open'))
 roots+=names
assert len(roots)==len(set(roots));modules=[r['module']for r in support]
(E/'SUPPORT.json').write_text(json.dumps(support,indent=2)+'\n');(E/'COMPILES.json').write_text(json.dumps(attempts,indent=2)+'\n')
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots),indent=2)+'\n')
s=Path('lean/PV_LIB_A_RawAudit8.lean').read_text();arrays='    (#[ '+', '.join('`'+m for m in modules)+'],\n     #[ '+', '.join('`'+r for r in roots)+'])'
s,n=re.subn(r'    \(#\[.*?\],\n     #\[.*?\]\)',lambda _:arrays,s,count=1,flags=re.S);assert n==1
Path('lean/PV_LIB_A_RawAudit9.lean').write_text(s)
old=json.loads(subprocess.check_output(['git','show',base+':'+str(M)]));current=json.loads(M.read_text());assert old['slots']==current['slots']and old['counts']==current['counts']
record=dict(base=base,legacy_definition='PV_LIB_StoreActionTable.v2',legacy_v2_unchanged=True,
 definition='PV_LIB_StoreActionTable.v2ProvenancePrograms',step='PV_LIB_StoreActionTable.v2ProvenanceStep',module='PV_LIB_A_StoreActionTable9',
 lifetime_step='PV_LIB_A_WeakOwnerFree9.step',lifetime_agreement='PV_LIB_A_WeakFreeAgreement9.agreement',source_state='PV_LIB_StoreActionTable.SourceState',
 option157='PV_LIB_A_OptionDestruct157.PV_THR2_LibrarySemantics_OptionDestruct157',actual_tail_bound='PV_LIB_StoreActionTable.hooks_tail_bound',
 allocator_provenance='PV_LIB_A_AllocatorProvenance',provider_allocator='PV_LIB_A_ProviderAllocator9',source_value_dispatch='PV_LIB_A_GenericDropMachine9',
 source_owner_backing='PV_LIB_A_ProviderBacking9.successful_backing',same_free_pointer='PV_LIB_A_ProviderBacking9.matching_free',
 lifetime='PV_LIB_A_FreeLifetime9',all_reply_source='PV_LIB_A_WeakFreeFacts9',
 emitted_typed_bodies_added=[218,315],named_opaque_semantics_added=[157,228],
 complete_table=False,complete_D984_adequacy=False,caller_histories_completed=False,allocation_byte_images_defined=0,D991_applied=True,
 support='lane-A/session9/SUPPORT.json',provenance='lane-A/session9/PROVENANCE.json',findings='lane-A/session9/MODEL_FINDINGS.md',raw_audit='lane-A/session9/RAW_AUDIT.json',
 slot_status_changes=0,endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0,
 remaining=['compose actual486/584/248/661 source runs with the Global weak-free resource step','payload/dynamic destructor and callback source effects for arbitrary T/nonempty hooks','generic allocation layout and sparse byte correspondence where required','collect4 and remaining opaque wrapper effects','Range93/f6/OwnInit corrected-machine caller histories'],
 qualification='PARTIAL. Option semantics bound; default allocator recovered from source values and provider; last-Weak source/OWNER lifetime graph and producer correspondence checked. No full last-strong/callback/caller-history closure.')
current['lane_A_session9']=record;M.write_text(json.dumps(current,indent=2)+'\n');(E/'MAP_DELTA.json').write_text(json.dumps(dict(base=base,slots_changed=[],metadata=record,counts_unchanged=current['counts']),indent=2)+'\n')
(E/'LAUNCH_FINDINGS.json').write_text(json.dumps(dict(range_extension='focused-host-s9.py differs from focused-host-s5.py only in the accepted-ID expression, adding55000-55089 focused and55090-55099 raw; compile-s9 routes evidence tosession9 and tightens current IDs',
 failures_before_compiler=[dict(attempt=55004,allocated=False,reason='local staging validation: nonexistent generated228 path stopped git add; no turn/host process'),dict(attempt=55006,allocated=True,reason='dependency resolution before elaboration; AllocatorProvenance had not passed yet; next dependent55009 used accepted55008')],
 failed_sources='Every proof/elaboration failure is archived as failed-ID.lean.xz and was repaired with different bytes; no failed source was rerun unchanged',
 no_infrastructure_stop=True,no_refusals=True),indent=2)+'\n')
print(len(modules),'modules;',len(roots),'new roots;',len(attempts),'compiler receipts; slot counts unchanged',current['counts'])
