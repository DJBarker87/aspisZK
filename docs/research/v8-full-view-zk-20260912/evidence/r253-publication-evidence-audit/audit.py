import hashlib,json,pathlib,re
BASE=pathlib.Path('docs/research/v8-full-view-zk-20260912'); EVID=BASE/'evidence'
SLUGS=['r251-current-private-add-sub','r252-current-private-complex-linear','r253-current-private-complex-norm']
EXPECTED_AXIOMS={'r251-current-private-add-sub':4,'r252-current-private-complex-linear':6,'r253-current-private-complex-norm':4}
EXPECTED_REJECTED={'r251-current-private-add-sub':3,'r252-current-private-complex-linear':0,'r253-current-private-complex-norm':1}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def axiom_lines(text):
    lines=text.splitlines(); out=[]; i=0
    while i<len(lines):
        if lines[i].startswith("'") and ' depends on axioms: [' in lines[i]:
            block=[lines[i]]
            while ']' not in block[-1]:
                i+=1
                if i>=len(lines):raise AssertionError('truncated axiom output')
                block.append(lines[i])
            out.append(' '.join(' '.join(block).split()))
        elif lines[i].startswith("'") and ' does not depend on any axioms' in lines[i]:
            out.append(' '.join(lines[i].split()))
        i+=1
    return out
reports=[]
for slug in SLUGS:
    p=EVID/slug;m=json.loads((p/'manifest.json').read_text()); sums=json.loads((p/'SHA256SUMS.json').read_text()); bad=[]
    for rel,h in sums.items():
        q=p/rel
        if not q.is_file():bad.append('missing:'+rel)
        elif sha(q)!=h:bad.append('hash:'+rel)
    actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q!=p/'SHA256SUMS.json'}
    unlisted=sorted(actual-set(sums));stale=sorted(set(sums)-actual)
    target=BASE/'lean'/m['target'];src=p/'source'/pathlib.Path(m['target']).name
    source_match=target.is_file() and src.is_file() and target.read_bytes()==src.read_bytes() and sha(src)==m['source_sha256']
    if not source_match:bad.append('target-source-copy-hash-mismatch')
    log=(p/m['log']).read_text(errors='replace'); observed=axiom_lines(log); expected=[' '.join(x.split()) for x in m['complete_print_axioms']]
    if observed!=expected:bad.append('complete-axiom-list-mismatch')
    axfile=(p/'axioms.txt').read_text()
    if axfile!='\n'.join(m['complete_print_axioms'])+'\n':bad.append('axioms-file-mismatch')
    if len(expected)!=EXPECTED_AXIOMS[slug]:bad.append('expected-axiom-count-mismatch')
    allowed={'propext','Classical.choice','Quot.sound'};foundation_only=True
    for entry in expected:
        found=set(re.findall(r'propext|Classical\.choice|Quot\.sound|sorryAx|native_decide',entry))
        if found-allowed or not found:foundation_only=False
    if not foundation_only:bad.append('unexpected-axiom-set')
    if 'sorryAx' in log:bad.append('sorryAx-in-success-log')
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',log);rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',log);sw=re.search(r'Swaps: (\d+)',log);ex=re.search(r'Exit status: (\d+)',log)
    metrics=bool(wall and rss and sw and ex and wall.group(1)==m['wall_time'] and int(rss.group(1))==m['peak_rss_kib'] and int(sw.group(1))==m['swaps'] and int(ex.group(1))==m['exit_status']==0)
    if not metrics:bad.append('successful-log-metrics-mismatch')
    res=m['resources'];runner=(p/'run_focus.py').read_text()
    scope=all(x in runner for x in [f"MemoryHigh={res['MemoryHigh']}",f"MemoryMax={res['MemoryMax']}",f"MemorySwapMax={res['MemorySwapMax']}",f"TasksMax={res['TasksMax']}",'systemd-run']) and all(x in runner for x in res['flags'].split())
    if not scope:bad.append('resource-scope-runner-mismatch')
    target_flags=pathlib.Path(m['target']).name in log and all(x in log for x in res['flags'].split())
    if not target_flags:bad.append('target-or-flags-not-in-good-log')
    rejected=[];rp=p/'rejected'
    if rp.exists():
        for f in sorted(rp.glob('*.log')):
            t=f.read_text(errors='replace');e=re.search(r'Exit status: (\d+)',t)
            rejected.append({'path':str(f.relative_to(p)),'exit_status':int(e.group(1)) if e else None,'sorryAx_present':'sorryAx' in t})
    if len(rejected)!=EXPECTED_REJECTED[slug]:bad.append('rejected-log-count-mismatch')
    if any(r['exit_status']!=1 or not r['sorryAx_present'] for r in rejected):bad.append('rejected-log-not-identified-sorryAx-draft')
    doc_name={'r251-current-private-add-sub':'R251_PRIVATE_ADD_SUB.md','r252-current-private-complex-linear':'R252_PRIVATE_COMPLEX_LINEAR.md','r253-current-private-complex-norm':'R253_PRIVATE_COMPLEX_NORM.md'}[slug]
    note=(BASE/doc_name).read_text()
    note_metrics=all(s in note for s in [m['source_revision'],m['wall_time'],str(m['peak_rss_kib']),str(m['swaps'])])
    note_scope='Full callback chronology, joint privacy and soundness remain open.' in note
    if not note_metrics or not note_scope:bad.append('note-metrics-or-scope-mismatch')
    reports.append({'bundle':slug,'target':m['target'],'source_revision':m['source_revision'],'source_sha256':m['source_sha256'],'exit_status':m['exit_status'],'wall_time':m['wall_time'],'peak_rss_kib':m['peak_rss_kib'],'swaps':m['swaps'],'checksum_count':len(sums),'checksum_errors':bad,'unlisted_files':unlisted,'stale_checksum_entries':stale,'target_source_copy_exact':source_match,'complete_axiom_log_exact':observed==expected,'axiom_count':len(expected),'axiom_foundations_only':foundation_only,'successful_log_metrics_exact':metrics,'resource_scope_runner_exact':scope,'target_and_flags_logged':target_flags,'note_scope_and_metrics_checked':note_metrics and note_scope,'rejected_logs':rejected,'manifest_boundary':m['proved_boundary']})
    assert not bad and not unlisted and not stale,(slug,bad,unlisted,stale)
assert [len(r['rejected_logs']) for r in reports]==[3,0,1]
assert [r['axiom_count'] for r in reports]==[4,6,4]
report={'status':'PASS_READ_ONLY_EVIDENCE_AUDIT','audited_at':'2026-10-02','bundles':reports,'scope':'Saved evidence consistency only. No Lean compile or regression run. No source-semantics/security release decision. No tracked edits.'}
out=pathlib.Path('.r21-scratch/r253-publication-evidence-audit/audit.json');out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'bundles':[{'bundle':r['bundle'],'checksums':r['checksum_count'],'axioms':r['axiom_count'],'rss':r['peak_rss_kib'],'wall':r['wall_time'],'swaps':r['swaps'],'rejected':r['rejected_logs']} for r in reports]},indent=2))
