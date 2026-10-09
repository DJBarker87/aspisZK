#!/usr/bin/env python3
"""Summarize retained measurements only; never executes a verifier."""
import json,hashlib,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
base=root/'results/r0-e2e-20261009';out=base/'re4'
summary={}
for stage in ['re3','s1','s2','s3','s4','s5d']:
    summary[stage]={}
    for f in ['transfer','withdrawal']:
        path=base/f're3/diagnostic/{f}-diagnostic-1.json' if stage=='re3' else out/f'{stage}-diagnostic/{f}-diagnostic-1.json'
        r=json.loads(path.read_text());totals={k:0 for k in ['Semantic','ChordClaims','Merkle','V1','V2']}
        for marker in r['phase_markers']:
            phase=marker['phase'];k={'semantic':'Semantic','chord-claims':'ChordClaims','v2':'V2'}.get(phase)
            if phase.startswith('merkle:'):k='Merkle'
            if phase.startswith('v1:'):k='V1'
            if k:totals[k]+=marker['delta_from_previous_cu']
        totals.update(Total=r['verifier_cu'],Outside=r['verifier_cu']-sum(totals.values()))
        summary[stage][f]={'phases':totals,'heap':r['sbf_heap_high_water_bytes'],'elf_sha256':r['elf_sha256'],'markers':r['phase_markers']}
(out/'summary-4.json').write_text(json.dumps({'selected':'s4','r91_audit':'s5d; regression, default off','stages':summary},indent=2)+'\n')
resources=[]
for p in sorted(out.glob('*.json')):
    r=json.loads(p.read_text())
    if r.get('schema')=='aspis.v8-state-only-cu.resources.v1':resources.append(dict(label=p.stem,**r))
(out/'resources-4.json').write_text(json.dumps(resources,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fixtures={}
for name in ['transfer.proof.bin','transfer.public.bin','withdrawal.proof.bin','withdrawal.public.bin']:
    assert (out/'fixtures'/name).read_bytes()==(base/'re3/fixtures'/name).read_bytes()
    assert (out/'regenerated'/name).read_bytes()==(out/'fixtures'/name).read_bytes()
    fixtures[name]=sha(out/'fixtures'/name)
a=json.loads((out/'fixtures/corruption-cases.json').read_text());b=json.loads((base/'re3/fixtures/corruption-cases.json').read_text());assert a==b and len(a)==1894
preservation={'rejections_identical_to_re3':True,'count':len(a),'fixtures_regenerated_byte_identical':fixtures,'selected_artifact':json.loads((out/'selected-artifact-equality.json').read_text())}
(out/'preservation-4.json').write_text(json.dumps(preservation,indent=2)+'\n')
# Full final resource/phase tables are generated from raw retained records.
lines=['| Stage | Fixture | Semantic | ChordClaims | Merkle ×22 | V1 ×22 | V2 | Total | Incremental saving |','|---|---|---:|---:|---:|---:|---:|---:|---:|']
previous={}
for stage,variants in summary.items():
    for f,r in variants.items():
        p=r['phases'];saving=previous.get(f,p['Total'])-p['Total'];previous[f]=p['Total']
        lines.append('| '+stage+' | '+f+' | '+' | '.join(f'{p[k]:,}' for k in ['Semantic','ChordClaims','Merkle','V1','V2','Total'])+f' | {saving:,} |')
(out/'phase-table.md').write_text('\n'.join(lines)+'\n')
lines=['| Job | Exit | Wall s | Peak aggregate RSS MiB | Cgroup peak MiB | Swap B |','|---|---:|---:|---:|---:|---:|']
for r in resources:
    n=r['label'];lines.append(f"| [{n}]({n}.json) | {r['exit_status']} | {r['wall_seconds']:.3f} | {r['peak_aggregate_rss_bytes_sampled']/2**20:.2f} | {r['cgroup_memory_peak_bytes']/2**20:.2f} | {r['cgroup_swap_current_bytes']} |")
(out/'resources-4.md').write_text('\n'.join(lines)+'\n')
print('\n'.join((out/'phase-table.md').read_text().splitlines()))
