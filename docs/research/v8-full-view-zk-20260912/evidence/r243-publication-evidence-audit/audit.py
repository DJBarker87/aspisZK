import hashlib,json,pathlib,re
BASE=pathlib.Path('docs/research/v8-full-view-zk-20260912')
EVID=BASE/'evidence'
SLUGS=['r239-current-coefficient-raw','r240-current-half-execution','r241-current-coefficient-execution','r242-current-line-coefficient-execution','r243-retained-line-norm-bridge']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def axioms_from_log(text):
    lines=text.splitlines(); found=[]; i=0
    while i<len(lines):
        if lines[i].startswith("'") and ' depends on axioms: [' in lines[i]:
            chunk=[lines[i]]
            while ']' not in chunk[-1]:
                i+=1
                if i>=len(lines): raise AssertionError('truncated axiom block')
                chunk.append(lines[i])
            found.append(' '.join(' '.join(chunk).split()))
        i+=1
    return found
reports=[]
for slug in SLUGS:
    p=EVID/slug; m=json.loads((p/'manifest.json').read_text()); sums=json.loads((p/'SHA256SUMS.json').read_text())
    bad=[]
    for rel,h in sums.items():
        q=p/rel
        if not q.is_file():bad.append('missing:'+rel)
        elif sha(q)!=h:bad.append('hash:'+rel)
    files={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q != p/'SHA256SUMS.json'}
    unlisted=sorted(files-set(sums)); stale=sorted(set(sums)-files)
    target=BASE/'lean'/m['target']; copied=p/'source'/pathlib.Path(m['target']).name
    source_equal=target.is_file() and copied.is_file() and target.read_bytes()==copied.read_bytes()
    if not source_equal:bad.append('source-copy-mismatch')
    good_log=p/m['log']; log=good_log.read_text(errors='replace')
    measured_axioms=axioms_from_log(log); expected_axioms=[' '.join(s.split()) for s in m['complete_print_axioms']]
    if measured_axioms!=expected_axioms:bad.append('axiom-log-mismatch')
    if (p/'axioms.txt').read_text()!='\n'.join(m['complete_print_axioms'])+'\n':bad.append('axioms-file-mismatch')
    # Check GNU time metrics and compiler target from the saved successful log.
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',log)
    rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)
    swap=re.search(r'Swaps: (\d+)',log); ex=re.search(r'Exit status: (\d+)',log)
    metric_ok=bool(wall and rss and swap and ex and wall.group(1)==m['wall_time'] and int(rss.group(1))==m['peak_rss_kib'] and int(swap.group(1))==m['swaps'] and int(ex.group(1))==m['exit_status']==0)
    if not metric_ok:bad.append('successful-log-metrics-mismatch')
    command_match=pathlib.Path(m['target']).name in log and '-j1 -M4500' in log
    if not command_match:bad.append('target-or-flags-not-in-log')
    rejected=[]
    rp=p/'rejected'
    if rp.exists():
        for f in sorted(rp.glob('*.log')):
            t=f.read_text(errors='replace'); e=re.search(r'Exit status: (\d+)',t)
            rejected.append({'log':str(f.relative_to(p)),'exit_status':int(e.group(1)) if e else None,'sorryAx_present':'sorryAx' in t})
    historical_rejections=[]
    if slug=='r239-current-coefficient-raw':
        hp=p/'provenance/r232-coefficient-translation'
        result=json.loads((hp/'result.json').read_text())
        historical_rejections.append({'artifact':'provenance/r232-coefficient-translation','child_exit_status':result['exit_status'],'generated_empty_translation':result['generated'],'rejected_for_source_proof': 'REJECTED for source-proof use' in (hp/'README.md').read_text()})
    ax_lists_ok=all(set(re.findall(r'propext|Classical\.choice|Quot\.sound',s)) <= {'propext','Classical.choice','Quot.sound'} and not any(z in s for z in ['sorryAx','native_decide','execution_assumption']) for s in expected_axioms)
    if not ax_lists_ok:bad.append('nonfoundation-axiom')
    doc=BASE/(slug.replace('r239-current-coefficient-raw','R239_CURRENT_COEFFICIENT_RAW.md').replace('r240-current-half-execution','R240_CURRENT_HALF_EXECUTION.md').replace('r241-current-coefficient-execution','R241_CURRENT_COEFFICIENT_EXECUTION.md').replace('r242-current-line-coefficient-execution','R242_CURRENT_LINE_COEFFICIENT_EXECUTION.md').replace('r243-retained-line-norm-bridge','R243_RETAINED_LINE_NORM_BRIDGE.md'))
    note=doc.read_text()
    docmetrics=all(v in note for v in [str(m['source_revision']),m['wall_time'],str(m['peak_rss_kib']),str(m['swaps'])])
    report={'evidence_dir':str(p),'target':m['target'],'source_revision_field':m['source_revision'],'source_sha256':m['source_sha256'],'exit_status':m['exit_status'],'wall_time':m['wall_time'],'peak_rss_kib':m['peak_rss_kib'],'swaps':m['swaps'],'manifest_hashes_checked':len(sums),'checksum_errors':bad,'unlisted_files':unlisted,'stale_checksum_entries':stale,'promoted_source_matches_evidence_copy':source_equal,'source_sha_matches_manifest':source_equal and sha(copied)==m['source_sha256'],'successful_log_matches_all_axioms':measured_axioms==expected_axioms,'axioms_file_matches_manifest':(p/'axioms.txt').read_text()=='\n'.join(m['complete_print_axioms'])+'\n','axiom_count':len(expected_axioms),'foundation_axioms_only':ax_lists_ok,'successful_log_metrics_match_manifest':metric_ok,'target_and_flags_visible_in_log':command_match,'doc_metrics_match_manifest':docmetrics,'rejected_logs':rejected,'historical_rejections':historical_rejections,'scope_text':m.get('proved_boundary')}
    reports.append(report)
# R239 checksum inventory intentionally includes the nested historical R232 sums file.
assert all(r['checksum_errors']==[] and r['unlisted_files']==[] and r['stale_checksum_entries']==[] for r in reports), reports
assert all(r['promoted_source_matches_evidence_copy'] and r['source_sha_matches_manifest'] and r['successful_log_matches_all_axioms'] and r['axioms_file_matches_manifest'] and r['foundation_axioms_only'] and r['successful_log_metrics_match_manifest'] and r['target_and_flags_visible_in_log'] and r['doc_metrics_match_manifest'] for r in reports), reports
# Parent supplied the launch-race fact: record it explicitly without changing docs.
report={'status':'PASS_WITH_R242_LAUNCH_BASE_CAVEAT','audited_at':'2026-10-02','audits':reports,'scope_language_review':{'R239':'Selected leaf definitions compile; no execution correspondence or security gate is claimed. R232 empty translation is retained as rejected evidence.','R240':'Selected half/scalar operations are related to their exact arithmetic; coefficient array, point t provenance and inverse routes remain open.','R241':'Coefficient leaves are proved for canonical inputs; private R110 fast path and full point/vector traversal remain open.','R242':'Line coefficient leaves keep t independent and assert no source-point provenance or circle condition; point-derived t and inverse routes remain open.','R243':'Composed arithmetic yields retained line norms under an explicit base-field circle premise; whole traversal, vector provenance, private path and optimized acceptance remain open. The notes retain full callback chronology/security as open.'},'r242_launch_interpretation':{'manifest_source_revision':'f3ffde1f52bab63d1d561515f06978c2bb097291','parent_reported_commit_during_ssh_job':'5192edfdd','interpretation':'f3ffde1f5 is the compile launch/base revision, not evidence that the entire checkout stayed at that exact HEAD for the whole SSH job. The compiled target draft SHA-256 is 970b61f44dbed87ef09d6ed7b95fbb4444d5904f867c0284356f363f1ab242fa and matches both promoted source copy and current promoted target. Treat the revision statement as a launch-base label; no mismatch in target bytes or saved successful log was found.'},'scope':'Read-only publication-evidence consistency audit. No builds, regressions, or source edits performed.'}
OUT=pathlib.Path('.r21-scratch/r243-publication-evidence-audit/audit.json');OUT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'bundles':[{'dir':r['evidence_dir'],'target':r['target'],'checksums':r['manifest_hashes_checked'],'axioms':r['axiom_count'],'metrics_ok':r['successful_log_metrics_match_manifest'],'rejected_logs':r['rejected_logs']} for r in reports],'r242_launch_interpretation':report['r242_launch_interpretation']},indent=2))
