from pathlib import Path
import json,lzma,hashlib,re,sys
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text())
idx=read(E/'NIS_INPUTS.json');rows=[];findings=[]
for item in read(E/'NIS_RERUN_PLAN.json'):
    a,old=item['attempt'],item['original'];p=E/a/'receipt.json'
    if not p.exists():raise RuntimeError('Rerun stage incomplete: '+a)
    r=read(p);cfg=read(E/(a+'.json'));isolation=read(E/(a+'-isolation.json'))
    prior=E.parent/('slice-d-entry5-20261107' if old.startswith('NIJ_') else 'slice-d-entry4-20261106')
    original=(prior/(old+'.json')).read_bytes();o=json.loads(original)
    assert cfg['original_config_sha256']==sha(original)==isolation['original_config_sha256']
    assert isolation['allowed'] is True
    assert r['env']['CARGO_TARGET_DIR']==r['native_command'][r['native_command'].index('--target-dir')+1]==str('/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target')
    # Every semantic native argument is identical; only manifest/output path changes.
    left=list(o['native_command']);right=list(r['native_command'])
    for flag in ['--manifest-path','--target-dir']:
        i=left.index(flag)+1;left[i]=right[i]='<OWNED_PATH>'
    assert left==right
    for k,v in o['env'].items():
        if k!='TMPDIR':assert r['env'][k]==v,(a,k)
    for n,h in r['source_hashes'].items():
        q=E/idx['objects'][h]['path'];assert sha(lzma.decompress(q.read_bytes()))==h
        assert idx['attempts'][a][n]==h
    assert read(E/(a+'-graph-check.json'))['graph_matches_frozen']
    assert read(E/(a+'-erasure-check.json'))['passed']
    assert read(E/(a+'-lock-check.json'))['unchanged']
    ad=read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
    previous=read(prior/old/'receipt.json')['exit_status'];negative=previous==1
    valid=r['exit_status']==previous and 'timed out' not in log.lower() and ('VERIFICATION:- SUCCESSFUL' in log if not negative else ('VERIFICATION:- FAILED' in log and re.search(r'\*\* 1 of \d+ failed',log) and 'Failed Checks:' in log and 'unwinding assertion' not in log))
    if not valid:findings.append(dict(id='NIS-F'+str(len(findings)+1),attempt=a,original=old,reason='Isolated semantic verdict differs; no reconciliation or unchanged replay',exit=r['exit_status']))
    rows.append(dict(attempt=a,original=old,original_config_sha256=sha(original),old_target=cfg['old_target'],new_target=r['env']['CARGO_TARGET_DIR'],exit=r['exit_status'],positive=not negative,semantic_verdict_reproduced=bool(valid),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
out=dict(status='PASS_ISOLATED_RERUN' if not findings else 'FINDINGS_NO_AUTOMATIC_CREDIT',configurations=rows,findings=findings,kmx_patch_sha256=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()),rows_pending_combined_gate=['TX2:202','TX1:NGB001','TX2:211'],new_rows_admitted=0)
(E/'NIS_RERUN.json').write_text(json.dumps(out,indent=1)+'\n')
text='# Isolated native reruns\n\nOriginal configuration SHA256 is retained byte-exactly; relocated serialized configurations have distinct hashes because source/output/temporary paths change. Native flags, features, harness names, property, source snapshots, optimizer and timeouts are identical. Explicit CARGO_TARGET_DIR and --target-dir agree inside NIS workspace; predecessor target is never reused.\n\n| NIS | Original | Old target | New target | Result | Kind |\n|---|---|---|---|---|---|\n'
for r in rows:text+=f"| {r['attempt']} | {r['original']} | `{r['old_target']}` | `{r['new_target']}` | {r['exit']} / {'reproduced' if r['semantic_verdict_reproduced'] else 'FINDING'} | {'pass' if r['positive'] else 'matched failing control'} |\n"
text+='\nExact original hashes and section6 resource/source records: NIS_RERUN.json, NIS_ATTEMPTS.jsonl and per-attempt receipts. Zero rows admitted before the canonical combined import / raw-axiom / NFX gate.\n'
(E/'NIS_RERUN.md').write_text(text)
print(json.dumps(dict(status=out['status'],runs=len(rows),findings=len(findings))))
sys.exit(bool(findings))
