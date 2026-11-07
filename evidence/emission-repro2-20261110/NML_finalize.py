"""Finalize receipt indices and source-candidate accounting; launches no tools."""
from pathlib import Path
import json,hashlib,subprocess,collections,re,lzma
E=Path(__file__).resolve().parent;load=lambda p:json.loads(p.read_text());write=lambda n,d:(E/n).write_text(json.dumps(d,indent=2)+'\n');sha=lambda b:hashlib.sha256(b).hexdigest()
def gitblob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def main():
 plan=load(E/'NML_PLAN.json');scope=[];phases=[]
 for p in sorted(E.glob('NML_[ELBA][0-9][0-9][0-9]/receipt.json')):
  r=load(p);scope.append({k:r[k] for k in ['attempt','kind','module','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms','cgroup_memory_peak_bytes']})
  if not r['attempt'].startswith('NML_B'):phases.append(dict(r,receipt=str(p.relative_to(E))))
 for p in sorted(E.glob('NML_E[0-9][0-9][0-9]/configuration_receipt.json')):phases.append(dict(load(p),receipt=str(p.relative_to(E))))
 write('NML_RUN_SUMMARY.json',dict(scopes=scope,configurations_and_Lean=phases,scope_wall_seconds=sum(r['wall_seconds'] for r in scope),configuration_and_Lean_wall_seconds=sum(r['wall_seconds'] for r in phases),maximum_process_rss_kib=max(int(r['peak_rss_kib']) for r in scope),all_scope_swaps_zero=all(int(r['swaps'])==0 for r in scope),warning='Scope totals and member totals overlap and are never summed together. E001 is excluded from credit. A001 reuses successful E009 Charon, no new Charon charge.'))
 events=[json.loads(l) for l in (E/'NML_ATTEMPTS.jsonl').read_text().splitlines()];seen={(r.get('attempt'),r.get('kind')) for r in events}
 with (E/'NML_ATTEMPTS.jsonl').open('a') as f:
  for r in phases:
   if r.get('scope_attempt') and (r['attempt'],'configuration_result') not in seen:f.write(json.dumps(dict(kind='configuration_result',attempt=r['attempt'],scope_attempt=r['scope_attempt'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],receipt=r['receipt']))+'\n')
 failures=[]
 for a,reason in [('NML_E009','Charon succeeded; frozen-native opacity metadata prefix rejected reference crate before Aeneas. Original failure retained; A001 resumed first Aeneas stage.'),('NML_E018','Pinned Aeneas internal shared-loan simplification error, interp/InterpBorrows.ml:2731, source src/lib.rs:14:1-14:37. No unchanged retry.'),('NML_E029','Archived command uses --locked; Cargo.lock absent from archived reference input. Charon exits101; no LLBC and no Aeneas. No flag relaxation or fabricated lock.'),('NML_A001','Strict corrected opacity validation passes; exact successful E009 LLBC reused (zero new Charon). First Aeneas run fails internal shared-loan simplification, interp/InterpBorrows.ml:2731, source lib.rs:114:12-117:13. No unchanged retry.')]:
  p=E/a/('configuration_receipt.json' if a.startswith('NML_E') else 'receipt.json');r=load(p);failures.append(dict(attempt=a,exit=r['exit_status'],reason=reason,receipt=str(p.relative_to(E)),stdout=a+'/stdout.log',source_revision=r['source_revision']))
 write('NML_TOOL_FAILURES.json',dict(excluded_protocol_attempt='NML_E001; NML_ADMISSION_FINDING.json',failures=failures))
 mp=load(E/'NML_INPUT_MAP.json');mp['materialized_inputs']=[]
 for q in plan['runs']:
  root=E/q['reference_directory'];src=root/q['source_relative'];mf=root/'Cargo.toml';mp['materialized_inputs'].append(dict(run=q['run'],source_path=str(src.relative_to(E)),source_git_blob=gitblob(src.read_bytes()),source_sha256=sha(src.read_bytes()),manifest_path=str(mf.relative_to(E)),manifest_git_blob=gitblob(mf.read_bytes()),manifest_sha256=sha(mf.read_bytes()),historical_basis=q['reference_basis'],manifest_basis=q['manifest_basis']))
 for g in mp['groups']:
  if g['group']=='NMH_G080':g['missing_input']='Historical --locked requires Cargo.lock, absent from archived package; E029 fails before LLBC.'
 write('NML_INPUT_MAP.json',mp)
 p=load(E/'NML_PROVENANCE.json');old=load(E.parent/'emission-repro-20261110/NMH_PROVENANCE.json');oldrows={r for b in old['blobs'] if b['verdict']!='REPRODUCED' for r in b['affected_CLOSED_rows']};newrows=set(p['conservative_affected_CLOSED_rows']);write('NML_ROW_IMPACT_DELTA.json',dict(method=p['impact_method'],before=len(oldrows),after=len(newrows),no_longer_matched=sorted(oldrows-newrows),newly_matched=sorted(newrows-oldrows),rootless_unassessed=p['rootless_CLOSED_unassessed'],ledger_changed=False))
 by={b['blob']:b for b in p['blobs']};groups={h:g for g in mp['groups'] for h in g['members']};categories={}
 for name,test in [('195_absent_reference_crate',lambda b:b['reason'].startswith('Emission names source/reference')),('81_missing_configuration',lambda b:b['reason'].startswith('Missing full historical'))]:
  bs=[b for b in old['blobs'] if test(b)];categories[name]=dict(total=len(bs),hash_linked_input_configuration_candidates=sum(bool(groups[b['blob']]['mappings']) for b in bs),additional_package_source_candidates=sum(bool(groups[b['blob']]['archive_sources']) and not groups[b['blob']]['mappings'] for b in bs),verdicts=dict(collections.Counter(by[b['blob']]['verdict'] for b in bs)))
 write('NML_RECOVERY_SUMMARY.json',dict(categories=categories,original_17_difference_classifications=dict(collections.Counter(b['classification'] for b in load(E/'NML_DIFFS_CLASSIFIED.json')['blobs'])),candidate_warning='A source/configuration candidate is not a verified original input for each blob until its output reproduces. Exact output equality earns the verdict; name proximity never does.'))
 print(json.dumps(dict(scopes=len(scope),configuration_or_Lean_receipts=len(phases),failed_members=len(failures),impact_before=len(oldrows),impact_after=len(newrows))))
if __name__=='__main__':main()
