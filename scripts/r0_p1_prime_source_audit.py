#!/usr/bin/env python3
"""Mechanical B copy audit. No protocol or source-refinement conclusion."""
import hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r0-cost-probe-20261009'
def tokens(s):
    s=re.sub(r'//[^\n]*','',s)
    return re.findall(r'\w+|[^\s]',s)
def clean(s):
    s=re.sub(r'    if diagnostic \{\s*(?:mark\("[^"]*"\);\s*)+\}', '', s)
    s=re.sub(r'mark\("[^"]*"\);','',s)
    s=s.replace('use super::mark;','').replace('use aspis_core::r0_probe::mark;','').replace('    diagnostic: bool,\n','')
    return s
rows=[]
ref=root/'crates/aspis-core/src/r0/onchain.rs'
probe=root/'crates/aspis-core/src/r0_probe/onchain.rs'
rows.append({'reference':str(ref.relative_to(root)),'probe':str(probe.relative_to(root)),'reference_sha256':hashlib.sha256(ref.read_bytes()).hexdigest(),'probe_sha256':hashlib.sha256(probe.read_bytes()).hexdigest(),'tokens_equal_after_removing_passive_markers_and_diagnostic_argument':tokens(ref.read_text())==tokens(clean(probe.read_text()))})
protected=['crates/aspis-core/src/r0/onchain.rs','crates/aspis-core/src/r0/prover.rs','crates/aspis-prover/src/r0.rs','crates/aspis-prover/src/r0_fixture.rs','crates/aspis-statement/src/r0.rs','crates/aspis-statement/src/state_only_verify.rs','crates/aspis-core/src/state_only_prefix.rs','crates/aspis-core/src/state_only_sumcheck.rs']
protected_rows=[]
for name in protected:
    base=subprocess.check_output(['git','show',f'bedd04207:{name}'],cwd=root)
    protected_rows.append({'path':name,'unchanged_from_base':base==(root/name).read_bytes(),'sha256':hashlib.sha256(base).hexdigest()})
changed=subprocess.check_output(['git','diff','--name-only','bedd04207'],cwd=root,text=True).splitlines()
record={'label':'COST PROBE: unproved; mechanical source-copy check only','copy_audit':rows,'protected_sources':protected_rows,'lean_diff_files':[p for p in changed if p.endswith('.lean')],'fixture_diff_files':[p for p in changed if 'fixture' in p]}
p=out/'b-source-copy-audit.json';assert not p.exists();p.write_text(json.dumps(record,indent=2)+'\n')
assert all(v['tokens_equal_after_removing_passive_markers_and_diagnostic_argument'] for v in rows),rows
assert all(v['unchanged_from_base'] for v in protected_rows)
assert not record['lean_diff_files'] and not record['fixture_diff_files']
print('S4 onchain arithmetic tokens match after removing B markers; all protected sources unchanged')
