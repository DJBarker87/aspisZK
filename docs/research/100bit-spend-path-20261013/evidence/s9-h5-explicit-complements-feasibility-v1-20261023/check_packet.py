from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent;base=r.parent.parent;m=json.loads((r/'manifest.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in m['files']:
 p=r/f['path'];assert h(p)==f['sha256'] and p.stat().st_size==f['bytes']
def span(p):
 s=p.read_text();i=s.index('fn state_only_statement_points(');a=s.index('{',i);d=1;j=a+1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i:j]
s=r/'sources';old=(s/'state_only_prefix.H5.rs').read_text();new=(s/'state_only_prefix.candidate.rs').read_text()
needle='    for coordinate in [7usize, 6] {\n        absorption[coordinate] = QM31::ONE.sub(absorption[coordinate]);\n    }'
assert old.count(needle)==1 and old.replace(needle,'    absorption[7] = QM31::ONE.sub(absorption[7]);\n    absorption[6] = QM31::ONE.sub(absorption[6]);')==new
assert span(s/'state_only_prefix.candidate.rs')==span(s/'state_only_prefix.extracted-v3-input.rs')
b=json.loads((r/'evidence/gates/sbf/receipt.json').read_text());assert b['exit_status']==0 and b['scope_swap_current_bytes_at_exit']==0 and b['watchdog'] is None
a=json.loads((r/'evidence/cache-recompile-assertions.json').read_text());assert len(a['asserted_compiled'])==3 and a['optimized_release'] and not a['identical']
g=json.loads((r/'evidence/gates/gate-result.json').read_text());assert len(g['six_fixture_rows'])==6 and g['all_six_approved_plus12214_pass'] and g['all_six_outputs_match'] and g['strict_stack_receipt']['exit_status']==0
f=json.loads((r/'evidence/full-mask-comparison.json').read_text());assert f['approved12214_pass'] and f['checkpoint_same_H5'] and f['return_same_H5'] and f['error'] is None
for x in json.loads((r/'source-dependencies.json').read_text())['reused_packets']:assert h(base/x['path'])==x['sha256']
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.so','.elf','.bin','.olean','.ilean','.ir','.llbc','.dylib','.dll'}
print('PASS: isolated H5 two ordered complements, exact V3 source-span reuse, measured gates within +12214; no adoption/security claim')
