import json
r=json.load(open('PCWR_SOURCE_SHA_AUDIT_raw.json'))
D='docs/research/100bit-spend-path-20261013/'
resolved={'11679ad2':'evidence/adapter-rw-20261023/lean-024/sources/AdapterRwModel.lean','4b6ac02f':'evidence/s1-current-wide-mul-canonical-20261020/diagnostics/rejected-v1/CurrentWideMulCanonical.lean','77dad259':'evidence/finish-install-20261026/FIn_034/sources/FIn_WeightsFuns.lean','500c583b':'evidence/finish-install-20261026/FIn_033/sources/FIn_WeightsTypes.lean','14e6b26f':'evidence/tx2-native5-20261107/NJC_L048/sources/NJC_generated/NJC_ReaderEmission.lean','ba38154a':'evidence/tx2-native5-20261107/NJC_L046/sources/NJC_generated/NJC_ReaderEmission.lean','0f62275e':'evidence/ports3-20261023/lean-049/sources/Port3_NativeBatchBody.lean','ae8ce534':'evidence/ports3-20261023/lean-056/sources/Port3_NativeGeometryBody.lean','451412b9':'evidence/port5q2-20261024/lean-039/sources/Port5Q2_ReaderWeights.lean'}
def isenum(o): return all(('PARTITION' in f or f.startswith('prov-plan') or f.startswith('prov-p0-')) for f in o['files'])
cit=[];enum=[]
for o in r['differences']:
    if o['kind']=='generator_input_copy_sha':
        o['cited_source_path']=D+resolved[o['cited_sha256'][:8]]
    (enum if isenum(o) else cit).append(o)
mods=sorted({o['module'] for o in enum})
out=dict(authority='l187_plan.json on host /home/dombarker/project-offloads/codex-cx-replay-l187-20261109 (by script; map of module->path,sha extracted, not copied)',
 scan='all .json/.md/.py/.sh/.txt/.jsonl and gate_*.lean under evidence/prov-p*/ on research (prov-p5h excluded); cited .lean paths resolved against git research and hashed (sha256); JSON objects with module+sha keys compared; gate_<Module>.lean generator input copies hashed',
 files_scanned=r['files_scanned'],modules_cited=r['modules_cited'],
 citations_differing_from_plan=cit,
 citation_count=len(cit),
 modules_differing=sorted({o['module'] for o in cit}),
 partition_enumeration_note='PARTITION.json files (prov-p0, p1a/b, p2a-d, p5, plan) enumerate every candidate blob per module including non-plan alternatives; those are plan inputs, not source citations of a generator. Count and module list only.',
 partition_enumeration_differing_entries=len(enum),partition_enumeration_modules=len(mods),
 same_sha_other_path_cites=r['same_sha_other_path'],
 caveats='sha_cite entries come from PCVB_STATUS.json only (module+blob keys); short-hash citations in prose (handoffs) found only by path, not by sha. A gate_<Module>.lean input copy differing from the plan source means the generator was fed that older/other source text, not necessarily that the proof statement is wrong: statements are against compiled gate constants.')
json.dump(out,open('PCWR_SOURCE_SHA_AUDIT.json','w'),indent=1)
print(len(cit),len(enum),len(mods))
