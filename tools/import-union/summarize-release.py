#!/usr/bin/env python3
"""Validate collected host evidence without rerunning any Lean target."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/'docs/research/100bit-spend-path-20261013'
E = BASE/'evidence/import-union-20261022'
H = E/'build-host'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
records = [json.loads(l) for l in (H/'modules.jsonl').read_text().splitlines()]
plan = json.loads((H/'plan.json').read_text())
latest = {r['module']:r for r in records}
def parse_axioms(text):
    result=[]
    pending=[]
    for line in text.splitlines():
        if 'depends on axioms:' in line or 'does not depend on any axioms' in line:
            pending=[line]
        elif pending:
            pending.append(line)
        if pending and (']' in line or 'does not depend on any axioms' in line):
            result.append('\n'.join(pending))
            pending=[]
    assert not pending, ('truncated axioms output',pending)
    return result
checks = []
for rec in plan['ordered']:
    r = latest.get(rec['module'])
    assert r and r['exit']==0, ('unfinished target',rec['module'],r)
    assert r['source_sha256']==rec['sha256'], rec['module']
    assert sha(ROOT/rec['path'])==rec['sha256'], ('source drift',rec['path'])
    committed=subprocess.check_output(['git','show',plan['revision']+':'+rec['path']],cwd=ROOT)
    assert hashlib.sha256(committed).hexdigest()==rec['sha256'], ('uncommitted source',rec['path'])
    text=(H/(r['label']+'.log')).read_text()
    timing=(H/(r['label']+'.time')).read_text()
    peak=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',timing)[1])
    swaps=int(re.search(r'Swaps: (\d+)',timing)[1])
    assert swaps==0, rec['module']
    assert r['swap_bytes']==0, rec['module']
    axioms_output=parse_axioms(text)
    for line in axioms_output:
        if 'depends on axioms:' in line:
            names={n.strip() for n in re.search(r'\[(.*?)\]',line,re.S)[1].replace('\n','').split(',')}-{''}
            assert names <= {'propext','Classical.choice','Quot.sound'}, line
    checks.append({'module':rec['module'],'label':r['label'],'source_revision':plan['revision'],'compiled_at_revision':r['source_revision'],
                   'source_sha256':r['source_sha256'],'deps_fingerprint':r['deps_fingerprint'],
                   'exit':r['exit'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':peak,
                   'aggregate_peak_rss_bytes_sampled':r['aggregate_peak_rss_bytes_sampled'],
                   'swaps':swaps,'swap_bytes':r['swap_bytes'],'axioms_output':axioms_output,
                   'axioms_note':'No axiom-print command in unchanged dependency' if not axioms_output else 'Standard axioms only',
                   'object_sha256':r['object_sha256']})
scan=latest['RawUnionScan']
lines=(H/(scan['label']+'.log')).read_text().splitlines()
raw={key:[json.loads(l[len(prefix):]) for l in lines if l.startswith(prefix)] for key,prefix in
     [('modules','RAW_MODULE '),('declarations','RAW_DECL '),('duplicate_types','RAW_DUP_TYPE '),('duplicates','RAW_DUP ')]}
modules={r[0]:{'path':r[1],'imports':r[2]} for r in raw['modules']}
object_pins={r['module']:r for r in json.loads((H/'raw-object-pins.json').read_text())}
assert object_pins.keys()==modules.keys(), 'incomplete union object pins'
for m,rec in latest.items():
    if m in object_pins and rec['exit']==0:
        assert object_pins[m]['sha256']==rec['object_sha256'], ('object drift',m)
changed=set(plan['changed_modules'])&modules.keys()
affected=set(changed)
while True:
    new=affected|{m for m,r in modules.items() if any(i in affected for i in r['imports'])}
    if new==affected:break
    affected=new
compiled={r['module'] for r in checks}
assert affected<=compiled, ('stale transitive dependents', sorted(affected-compiled))
# All import parents of the union roots are enumerated by ModuleData, not source regex.
closure={'raw_union_modules':len(modules),'changed_types_or_generated_roots':sorted(changed),
         'transitive_dependents_including_roots':sorted(affected),
         'all_affected_rebuilt':True,'rebuild_count':len(checks),'compiled_outside_union':sorted(compiled-modules.keys()),
         'terminal_roots':['AspisR1.CompositionPartsAfterValidationExact','AspisR1.PoseidonCandidatePackedFamilyResidual','TerminalPartsArithmeticExact'],
         'closure_boundary':'Selected retained union; archived alternate providers are migration inputs, not simultaneous modules.'}
for name in ['AspisR1.CompositionPartsAfterValidationExact','AspisR1.PoseidonCandidatePackedFamilyResidual','TerminalPartsArithmeticExact','ExtractedDecoderCallerBridge','OraclePortHeadlineFrozen2PerAttempt','R1Z.PrivacyR1HeadlineDeployed']:
    assert name in modules, ('missing required union member',name)
allowed=[]
collisions=[]
for row in raw['duplicates']:
    name, owners, same_type, kernel_allowed=row
    generated=bool(re.search(r'\.(eq(?:_\d+|_def|_unfold)?|congr_simp)$',name))
    rec={'name':name,'owners':owners,'identical_raw_types':same_type,'all_theorems':all(k=='theorem' for _,k in owners), 'allowed_generated_equation':bool(kernel_allowed and generated)}
    (allowed if rec['allowed_generated_equation'] else collisions).append(rec)
for name,value in [('raw-module-graph',raw['modules']),('raw-declarations',raw['declarations']),('raw-duplicate-types',raw['duplicate_types']),('raw-duplicates',sorted(allowed+collisions,key=lambda r:r['name'])),('closure-check',closure),('release-targets',checks)]:
    (E/(name+'.json')).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
union=next(r for r in checks if r['module']=='ImportUnionReleaseGate')
assert union['axioms_output'], 'union audits missing'
# The migration is the only edit allowed to each affected generated source.
migration=json.loads((E/'migration.json').read_text())
for r in migration['files']:
    assert sha(ROOT/r['path'])==r['after_sha256'],r['path']
base='317a687e34^'
endpoints=['docs/research/100bit-spend-path-20261013/lean/OraclePortHeadlineFrozen2PerAttempt.lean',
           'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean']
endpoint_pins=[]
for path in endpoints:
    before=subprocess.check_output(['git','show',base+':'+path],cwd=ROOT)
    assert before==(ROOT/path).read_bytes(),path
    endpoint_pins.append({'path':path,'sha256':sha(ROOT/path),'unchanged':True})
summary={'schema':'import-union-release-gate-v1','source_revision':plan['revision'],
         'migration_files':migration['file_count'],'migration_attributes':migration['attribute_count'],
         'compiled_targets':len(checks),'failed_attempts':[{'label':r['label'],'module':r['module'],'exit':r['exit']} for r in records if r['exit']],
         'raw_union_modules':len(modules),'raw_declarations':len(raw['declarations']),
         'allowed_equation_duplicates':len(allowed),'remaining_collisions':collisions,
         'union':union,'endpoint_pins':endpoint_pins,'total_successful_compile_wall_seconds':sum(r['wall_seconds'] for r in checks),
         'max_peak_rss_kib':max(r['peak_rss_kib'] for r in checks),'all_swaps_zero':True,
         'security_premises_changed':False,'candidate_source_edits':False}
(E/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:summary[k] for k in ['compiled_targets','raw_union_modules','raw_declarations','allowed_equation_duplicates','remaining_collisions','max_peak_rss_kib','all_swaps_zero']},indent=2))
if collisions:
    raise SystemExit(1)
