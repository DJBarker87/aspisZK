import hashlib,json,re
from pathlib import Path
E=Path(__file__).resolve().parent
ROOT=E.parents[4]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
final={
 'BinSourceCommitmentWords':'words-v2',
 'BinSourceCommitmentFrames':'frames-v3',
 'BinSourceCommitmentLiteral':'literal-v3',
 'BinSourceCommitmentOpening':'opening-v1',
 'BinStage2FoldedWord':'stage2-v3',
 'RawSourceDigestLog':'dep-log-v1',
 'RawSourceGlobalOracleCoupling':'dep-coupling-v1',
 'RawSourceGlobalOracleInitial':'dep-initial-v1',
}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((E/'source-pins.json').read_text())
for pin in pins['files']:
 assert sha(ROOT/pin['path'])==pin['sha256'],pin['path']
raw=(BASE/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean').read_text()
a=raw.index('def verifier.candidate.batch_leaf\n')
z=raw.index('/-- [aspis_r1_cost_probe::verifier::candidate::same_batch_leaf]',a)
leaf=raw[a:z].replace('def verifier.candidate.batch_leaf','def verifier.candidate.batch_leafWithWireOps').replace('  {H : Type}', '  (ops : LeafOps)\n  {H : Type}').replace('aspis_core.r0.merkle.C1_TAG','ops.c1Tag').replace('aspis_core.r0.merkle.C2_TAG','ops.c2Tag').replace('aspis_core.state_only_private_merkle.private_leaf_hash_with_digest\n      aspis_coredigestDigest32Inst hash','ops.leaf\n      aspis_coredigestDigest32Inst hash')
old='    let r ←\n      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s\n    let salt ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r'
assert leaf.count(old)==3
leaf=leaf.replace(old,'    let salt ← ops.salt s')
assert leaf in (BASE/'lean/WireTx2LeafBodies.lean').read_text()
rows=[]
for mod,attempt in final.items():
 src=BASE/'lean'/f'{mod}.lean'
 r=json.loads((E/attempt/'receipt.json').read_text())
 assert r['exit']==0,(mod,r['exit'])
 assert r['source_sha256']==sha(src),mod
 output=(E/attempt/'stdout.log').read_text()
 assert not re.search(r'\berror\b|sorryAx',output),mod
 reports=re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",output)
 names=[re.search(r"'([^']+)'",a).group(1).split('.')[-1] for a in reports]
 decls=re.findall(r'^\s*(?:private )?theorem\s+(\w+)',src.read_text(),re.M)
 assert sorted(names)==sorted(decls),(mod,names,decls)
 for a in reports:
  deps=re.search(r'\[([^\]]*)\]',a)
  assert not deps or set(re.sub(r'\s','',deps.group(1)).split(','))<={'propext','Classical.choice','Quot.sound'},a
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',src.read_text()),mod
 for dep,d in r['imports'].items():
  assert not d.get('missing'),(mod,dep)
  assert sha(Path(d['path']))==d['sha256'],(mod,dep,'dependency changed')
 obj=Path(r['argv'][r['argv'].index('-o')+1])
 r.update(axioms=reports,theorems=decls,source=str(src.relative_to(ROOT)),object_sha256=sha(obj),object_size_bytes=obj.stat().st_size)
 rows.append(r)
manifest={'schema':'focused-extractor-proof-packet-v1','scope':'focused conditional source adapters; not a clean release replay','modules':rows,'new_module_count':5,'new_theorem_count':sum(len(r['theorems']) for r in rows[:5]),'peak_rss_bytes':max(r['peak_rss_bytes'] for r in rows),'wall_seconds':sum(r['wall_seconds'] for r in rows),'swaps':sum(r['swaps'] for r in rows),'historical_attempts':[str(p.parent.name) for p in sorted(E.glob('*/receipt.json')) if p.parent.name not in final.values()]}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:manifest[k] for k in ['new_module_count','new_theorem_count','peak_rss_bytes','wall_seconds','swaps']}))
