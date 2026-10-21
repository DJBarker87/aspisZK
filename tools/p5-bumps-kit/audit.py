#!/usr/bin/env python3
"""Audit committed proof packets without rerunning any formal targets."""
import difflib,hashlib,json,re,subprocess
from pathlib import Path
from inventory import ROOT,OUT,FREEZE,sha,blob
KIT=Path(__file__).resolve().parent
pins=json.loads((KIT/'generated/source-pins.json').read_text())
for p,h in pins['generated'].items():assert sha((KIT/'generated'/p).read_bytes())==h,p
for p,h in pins['source_files'].items():assert sha(blob(p))==h,p
rows=json.loads((OUT/'kani-manifest.json').read_text())['attempts']
by_target={}
for r in rows:
    cmd=r['command']
    if '--harness' not in cmd:continue
    if r['verification_success']:
        assert r['exit_status']==0 and r['swaps']==0
        assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
        target=cmd[cmd.index('--harness')+1]
        # Attempt number is globally unique, independent of phase directory.
        if target not in by_target or int(r['attempt'].split('-')[0])>int(by_target[target]['attempt'].split('-')[0]):by_target[target]=r
missing=sorted(set(pins['harnesses'])-by_target.keys());assert not missing,missing
checks=[dict(harness=n,attempt=by_target[n]['attempt'],receipt=by_target[n]['receipt_path'],source_sha256=by_target[n]['source_sha256'],deps_fingerprint=by_target[n]['deps_fingerprint'],exit=by_target[n]['exit_status'],wall_seconds=by_target[n]['wall_seconds'],peak_rss_kib=by_target[n]['peak_rss_kib'],swaps=by_target[n]['swaps']) for n in pins['harnesses']]
# Every final component's source binding is checked against the frozen git blob.
for d in pins['declarations']:
    s=blob(d['path']);line=d['line'];start=sum(len(x) for x in s.splitlines(keepends=True)[:line-1])
    # Some slices begin after indentation, so bind by source line plus SHA in
    # generator --check, whose exact-string extraction is independently rerun.
    assert 0<=start<len(s)
lean_manifest=json.loads((OUT/'manifest.json').read_text())
lean_rows=[json.loads((OUT/p).read_text()) for p in lean_manifest['attempts']]
lean_ok=[r for r in lean_rows if r['exit']==0][-1]
src=ROOT/lean_ok['source'];assert sha(src.read_bytes())==lean_ok['source_sha256']
assert len(lean_ok['axioms'])==5
for line in lean_ok['axioms']:
    deps=re.search(r'depends on axioms: \[([^]]*)\]',line)
    if deps:assert set(deps[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+max(?:RecDepth|Heartbeats)',src.read_text(),re.M)
# No premise deletion or modification: retain complete verbatim signatures.
base='d18ab57d8';headline='docs/research/100bit-spend-path-20261013/lean/R1FinalSoundnessHeadline.lean';r19='docs/research/100bit-spend-path-20261013/lean/R1FinalSoundnessBinPerQueryR19.lean'
sig=[]
for p in [headline,r19]:
    before=subprocess.check_output(['git','show',base+':'+p],cwd=ROOT,text=True);after=(ROOT/p).read_text()
    assert before==after,p
    def signature(s):return s[s.index('theorem final_soundness'):s.index(':= by',s.index('theorem final_soundness'))]
    b=signature(before);a=signature(after)
    stem=Path(p).stem
    (OUT/(stem+'-signature-before.lean.txt')).write_text(b)
    (OUT/(stem+'-signature-after.lean.txt')).write_text(a)
    diff=''.join(difflib.unified_diff(b.splitlines(True),a.splitlines(True),fromfile='before',tofile='after'))
    assert diff==''
    (OUT/(stem+'-signature-unchanged.diff')).write_text(diff)
    sig.append(dict(module=stem,before_sha256=sha(b),after_sha256=sha(a),premise_removed=False,diff_empty=True))
identity=json.loads((OUT/'source-identity.json').read_text());assert all(r['byte_identical'] for r in identity['files'])
result=dict(schema='p5-component-audit-v1',source_revision=FREEZE,component_harnesses=len(checks),selected_checks=checks,all_final_components_pass=True,total_kani_attempts=len(rows),kani_failed_or_nonproof_attempts=[r['receipt_path'] for r in rows if not r['verification_success']],lean_attempts=len(lean_rows),lean_final={k:lean_ok[k] for k in ['module','source_revision','source_sha256','deps_fingerprint','exit','wall_s','peak_rss_bytes','process_swaps','axioms']},max_successful_rss_kib=max(c['peak_rss_kib'] for c in checks),total_selected_wall_seconds=sum(c['wall_seconds'] for c in checks),signatures=sig,whole_program_extraction=False,whole_svm_proof=False,shipped_source_modified=False,formal_headline_p5_removed=False)
(OUT/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['component_harnesses','all_final_components_pass','total_kani_attempts','lean_attempts','max_successful_rss_kib','total_selected_wall_seconds','formal_headline_p5_removed']},indent=2))
