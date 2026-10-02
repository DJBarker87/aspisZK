#!/usr/bin/env python3
"""Read-only publication evidence checks for R264/R265/R270."""
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'docs/research/v8-full-view-zk-20260912'
EVID=BASE/'evidence'
OUT=ROOT/'.r21-scratch/r270-publication-evidence-audit'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(s): return re.sub(r'\s+',' ',s).strip()
def decls(text):
    starts=[m.start() for m in re.finditer(r'(?m)^/--',text)]
    out={}
    for i,start in enumerate(starts):
        end=starts[i+1] if i+1<len(starts) else len(text)
        b=text[start:end].strip()
        b=re.split(r'(?m)^#print axioms ',b,maxsplit=1)[0].strip()
        b=re.sub(r'\nend AspisR\d+\w*\s*$','',b).strip()
        m=re.search(r'(?m)^.*?\b(?:def|structure)\s*\n?\s*([\w.]+)',b)
        if m: out[m.group(1)]=b
    return out
def body(s):
    m=re.search(r'(?m)^.*?\b(def|structure)\s+',s)
    if not m: raise ValueError('declaration start missing')
    return s[m.start(1):]
def axiom_lines(text):
    pattern=r"'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^\]]*\])"
    return [re.sub(r'\s+',' ',m.group(0)).strip() for m in re.finditer(pattern,text,re.S)]
def axioms_file_lines(text):
    rows=[]; current=[]
    for line in text.splitlines():
        if line.startswith("'") and current:
            rows.append(re.sub(r'\s+',' ',' '.join(current)).strip()); current=[]
        if line.strip(): current.append(line.strip())
        if current and ']' in line:
            rows.append(re.sub(r'\s+',' ',' '.join(current)).strip()); current=[]
    if current: rows.append(re.sub(r'\s+',' ',' '.join(current)).strip())
    return rows
def get_time(text, pattern):
    m=re.search(pattern,text,re.M)
    if not m: raise ValueError('missing metric '+pattern)
    return m.group(1)

bundles={
 'R264':'r264-current-private-coefficient-raw',
 'R265':'r265-current-private-norm-closures',
 'R270':'r270-current-private-coefficient-execution',
}
report={'audit':'saved publication evidence; no Lean or replay run','bundles':{},'raw_binding_audit':{},'checks':[]}
for label,dirname in bundles.items():
    d=EVID/dirname
    m=json.loads((d/'manifest.json').read_text())
    sums=json.loads((d/'SHA256SUMS.json').read_text())
    actual={p.relative_to(d).as_posix() for p in d.rglob('*') if p.is_file() and p.name!='SHA256SUMS.json'}
    missing=sorted(set(sums)-actual); unlisted=sorted(actual-set(sums))
    mismatches={rel:{'expected':expected,'actual':sha(d/rel)} for rel,expected in sums.items() if not (d/rel).is_file() or sha(d/rel)!=expected}
    source_path=d/'source'/Path(m['target']).name
    promoted=BASE/'lean'/m['target']
    log=d/m['log']; text=log.read_text(errors='replace')
    observed_axioms=axiom_lines(text)
    expected_axioms=[re.sub(r'\s+',' ',x).strip() for x in m['complete_print_axioms']]
    metric={
      'exit_status':int(get_time(text,r'Exit status: ([0-9]+)')),
      'wall_time':get_time(text,r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)'),
      'peak_rss_kib':int(get_time(text,r'Maximum resident set size \(kbytes\): ([0-9]+)')),
      'swaps':int(get_time(text,r'Swaps: ([0-9]+)')),
    }
    runner=(d/'run_focus.py').read_text()
    bundle={
      'manifest_target':m['target'],'source_revision':m['source_revision'],
      'manifest_source_sha256':m['source_sha256'],
      'source_copy_present':source_path.is_file(),
      'source_copy_sha256':sha(source_path) if source_path.is_file() else None,
      'promoted_target_present':promoted.is_file(),
      'promoted_target_sha256':sha(promoted) if promoted.is_file() else None,
      'copy_equals_promoted':source_path.is_file() and promoted.is_file() and source_path.read_bytes()==promoted.read_bytes(),
      'checksums':{'listed':len(sums),'missing':missing,'unlisted':unlisted,'mismatches':mismatches},
      'compile':{'manifest_exit':m['exit_status'],'observed':metric,'manifest_wall':m['wall_time'],'manifest_peak_rss_kib':m['peak_rss_kib'],'manifest_swaps':m['swaps'],'good_log':m['log']},
      'axioms':{'expected_count':len(expected_axioms),'observed_count':len(observed_axioms),'match':expected_axioms==observed_axioms,'expected':expected_axioms,'observed':observed_axioms,'axioms_txt_matches':axioms_file_lines((d/'axioms.txt').read_text())==expected_axioms,'sorryAx_in_good_log':'sorryAx' in text},
      'resources':m['resources'],'runner_mentions_caps':all(x in runner for x in ['MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128']),
      'runner_mentions_lean_flags':'-j1' in runner and '-M4500' in runner,
    }
    expected_metrics=(m['exit_status']==metric['exit_status'] and m['wall_time']==metric['wall_time'] and m['peak_rss_kib']==metric['peak_rss_kib'] and m['swaps']==metric['swaps'])
    bundle['pass_checksums']=not missing and not unlisted and not mismatches
    bundle['pass_source_identity']=bundle['copy_equals_promoted'] and bundle['source_copy_sha256']==m['source_sha256']
    bundle['pass_metrics']=expected_metrics
    bundle['pass_axioms']=bundle['axioms']['match'] and bundle['axioms']['axioms_txt_matches'] and not bundle['axioms']['sorryAx_in_good_log']
    report['bundles'][label]=bundle

# R264 accepted log is explicitly the seven-request complete run. The earlier
# declaration-only artifact has no #print outputs and cannot satisfy the audit.
r264=EVID/'r264-current-private-coefficient-raw'
r264m=json.loads((r264/'manifest.json').read_text())
old=(r264/'logs/declaration-only-no-axioms.log').read_text(errors='replace')
cur=(BASE/'lean'/r264m['target']).read_text()
report['r264_prior_attempt']={
 'earlier_log':'logs/declaration-only-no-axioms.log',
 'earlier_log_has_axiom_report':bool(axiom_lines(old)),
 'current_source_print_axiom_count':len(re.findall(r'(?m)^#print axioms ',cur)),
 'accepted_log':r264m['log'],
 'accepted_log_axiom_report_count':len(axiom_lines((r264/r264m['log']).read_text(errors='replace'))),
 'acceptance_basis':'Only the later successful log 1790913747557849000, whose source includes all seven #print axioms requests; declaration-only run is incomplete.'
}

# Independently check the recorded R264 seven copied blocks and 24 helper
# body comparisons against their actual saved input files/targets.
bdir=r264/'provenance/r264-raw'
ba=json.loads((bdir/'binding-audit.json').read_text())
for rel,h in ba['input_sha256'].items():
    p=ROOT/rel
    if not p.is_file() or sha(p)!=h: raise AssertionError(f'R264 binding input hash mismatch: {rel}')
for rel,h in ba['output_sha256'].items():
    p=bdir/rel
    if not p.is_file() or sha(p)!=h: raise AssertionError(f'R264 binding output hash mismatch: {rel}')
# Binding audit's internal checksum inventory is verified too.
bsums={line.split('  ',1)[1]:line.split('  ',1)[0] for line in (bdir/'binding-audit.SHA256SUMS').read_text().splitlines()}
for rel,h in bsums.items():
    p=ROOT/rel
    if not p.is_file() or sha(p)!=h: raise AssertionError(f'R264 binding audit checksum mismatch: {rel}')
inputs=ba['input_sha256']
genF=(ROOT/'.r21-scratch/r263-private-coefficient-translation/generated/AspisR263PrivateCoefficient/Funs.lean').read_text()
genT=(ROOT/'.r21-scratch/r263-private-coefficient-translation/generated/AspisR263PrivateCoefficient/Types.lean').read_text()
r249=(ROOT/'.r21-scratch/r249-r110-raw/AspisR249R110Raw.lean').read_text()
r259=(ROOT/'.r21-scratch/r259-private-input-raw/AspisR259PrivateInputRaw.lean').read_text()
r156F=(BASE/'lean/AspisR156FullFreeze/FunsCore.lean').read_text()
r156T=(BASE/'lean/AspisR156FullFreeze/Types.lean').read_text()
adapter=(bdir/'AspisR264PrivateCoefficientRaw.lean').read_text()
fd,td=decls(genF),decls(genT)
ad=decls(adapter)
raw_selected=[]
for n in ba['selected_aliases']:
    raw_selected.append((n,td[n],ad[n]))
for n in ba['selected_functions']:
    raw_selected.append((n,fd[n],ad[n]))
selected_equal=all(a==b for _,a,b in raw_selected)
# Recompute helper body comparisons from audited declarations.
r249d,r259d,r156fd,r156td=map(decls,[r249,r259,r156F,r156T])
helper_rows=[]; helper_mismatches=[]
for row in ba['helper_body_checks']:
    n=row['name']; tgt=row['target']
    if tgt=='R156': source=fd[n]; target=r156fd[n]
    elif tgt=='R249.Types': source=td[n]; target=r249d[n]
    elif tgt=='R259': source=fd[n]; target=r259d[n]
    elif tgt=='R249':
        source=fd[n]; target=r249d[n]
    else: raise AssertionError(f'Unexpected R264 helper target {tgt}')
    left=norm(body(source)); right=norm(body(target))
    for adp in row.get('documented_adaptations',[]):
        oldtoken,newtoken=adp['from'],adp['to']
        if left.count(oldtoken)!=adp['count']:
            helper_mismatches.append({'name':n,'reason':'adaptation count mismatch','adaptation':adp})
        left=left.replace(oldtoken,newtoken)
    match=left==right
    helper_rows.append({'name':n,'target':tgt,'matches_after_listed_adaptations':match})
    if not match: helper_mismatches.append({'name':n,'reason':'body differs after listed adaptations'})
qm=ba['QM31_R156_representation_check']
report['raw_binding_audit']={
 'binding_audit_checksums_valid':True,'input_hashes_valid':True,'output_hashes_valid':True,
 'selected_declarations':len(raw_selected),'selected_blocks_byte_equal_to_generated':selected_equal,
 'selected_report_count':len(ba['selected_body_checks']),'selected_report_all_exact':all(x['exact_block_copy'] and x['adaptation_count']==0 for x in ba['selected_body_checks']),
 'transitive_helper_bindings_reported':len(ba['helper_body_checks']),
 'helper_checks_independently_recomputed':len(helper_rows),'helper_mismatches':helper_mismatches,
 'qm31_normalized_equal_to_R156':qm['normalized_equal'],'qm31_local_shadow_declared':qm['local_shadow_declared'],
 'binding_audit_unresolved':ba['unresolved_mismatches'],
}

# Rejected R270 failed attempt is preserved and not counted as accepted evidence.
r270=EVID/'r270-current-private-coefficient-execution'
rej=(r270/'rejected/aspis-focus-1790913879265700000.log').read_text(errors='replace')
report['r270_rejected_attempt']={
 'log':'rejected/aspis-focus-1790913879265700000.log',
 'README_identifies_failed_array_rewrite_and_sorryAx':'sorryAx' in (r270/'rejected/README.md').read_text(),
 'exit_status':get_time(rej,r'Exit status: ([0-9]+)'),
 'sorryAx_present':'sorryAx' in rej,
 'accepted_target_is_successful_separate_log':True,
}

# Compact assertions capture the mechanical audit pass/fail conditions.
failed=[]
for k,v in report['bundles'].items():
    for field in ['pass_checksums','pass_source_identity','pass_metrics','pass_axioms','runner_mentions_caps','runner_mentions_lean_flags']:
        if not v[field]: failed.append(f'{k}.{field}')
if not report['raw_binding_audit']['selected_blocks_byte_equal_to_generated']: failed.append('R264 selected raw source blocks')
if report['raw_binding_audit']['helper_mismatches']: failed.append('R264 helper comparison')
if report['raw_binding_audit']['binding_audit_unresolved']: failed.append('R264 unresolved helper mismatch')
if report['r264_prior_attempt']['earlier_log_has_axiom_report']: failed.append('R264 earlier declaration-only log unexpectedly has reports')
if report['r264_prior_attempt']['current_source_print_axiom_count']!=7 or report['r264_prior_attempt']['accepted_log_axiom_report_count']!=7: failed.append('R264 accepted seven-report audit')
if report['r270_rejected_attempt']['exit_status']!='1' or not report['r270_rejected_attempt']['sorryAx_present']: failed.append('R270 rejected draft classification')
report['failed_checks']=failed
report['status']='PASS' if not failed else 'FAIL'
(OUT/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'failed_checks':failed,
 'bundles':{k:{'checksums':v['pass_checksums'],'source':v['pass_source_identity'],'metrics':v['pass_metrics'],'axioms':v['pass_axioms'],'axiom_count':v['axioms']['observed_count'],'resource_caps':v['runner_mentions_caps']} for k,v in report['bundles'].items()},
 'r264_binding':report['raw_binding_audit'], 'r264_attempt':report['r264_prior_attempt'], 'r270_rejected':report['r270_rejected_attempt']},indent=2))
if failed: raise SystemExit(1)
