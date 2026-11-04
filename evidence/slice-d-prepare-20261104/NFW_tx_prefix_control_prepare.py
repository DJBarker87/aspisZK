from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';src=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/candidate.rs'],cwd=R,text=True)
def body(signature,stop):
 a=src.index(signature);start=src.index('{',a);end=src.index(stop,start);return src[start+1:end]
a=body('pub fn tx1<H: Digest32>','    pending.finish(&mut a.weights);')
b=body('fn tx2_common<H: Digest32>','    // End the loop accumulator borrow')
common=lambda s:s.replace('batch_merkle(proof,','ops.merkle(proof,').replace('QueryGeometry::for_range','ops.geometry').replace('BatchedWeights::new','ops.pending').replace('query_loop(proof,','ops.query(proof,').replace('    let pending =','    ops.geometry_address=&geometry as *const _ as usize;\n    let pending =').replace('    batch_merkle(proof,','    ops.merkle(proof,')
na=common(a).replace('parse_shape(proof)','ops.shape(proof)').replace('canonical_scan(proof)','ops.scan(proof)').replace('prepare(public,','ops.prepare(public,').replace('Accumulator::new','ops.accumulator')
nb=common(b).replace('resume(checkpoint,','ops.resume(checkpoint,').replace('powers::<29>(p.gamma)','ops.powers(p.gamma)').replace('E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0])','ops.inactive(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0])').replace('    mark(obs, Phase::CheckpointRead);','    ops.g_address=g.as_ptr() as usize;\n    mark(obs, Phase::CheckpointRead);')
# Both prefixes observe the literal source folded-root local after its binding.
for name in ['na','nb']:
 s=locals()[name];s=s.replace('    ops.merkle(proof,','    ops.folded_address=folded_root.as_ptr() as usize;\n    ops.merkle(proof,');locals()[name]=s
text=(E/'NFW_tx_prefix_control.rs.txt').read_text().replace('NFW_TX1_PREFIX',na+'\n    Ok(())\n').replace('NFW_TX2_PREFIX',nb+'\n    Ok(())\n')
p=E/'NFW_prefix_prepare.py';s=p.read_text();pos=s.index('for name,stub in');s=s[:pos]+'candidate+='+repr(text)+'\n'+s[pos:]
s=s.replace('"spine_check" if name=="prepare_error" else name','"spine_check" if name=="prepare_error" else "tx1_prefix_check" if name=="tx1_error" else "tx2_prefix_check"')
p.write_text(s)
(E/'NFW_TX_PREFIX_SOURCE.json').write_text(json.dumps(dict(frozen_revision=F,tx1_original_prefix=a,tx1_local_record_prefix=na,tx2_original_prefix=b,tx2_local_record_prefix=nb,stop='At the query_loop call entry, before callee execution; no checkpoint or finish implementation entered.',scope='Failure-stage/control, same typed argument locations and selected producer frames. Proof backing is zeroed57607; child data meanings and all-byte/native-model associations remain OPEN. No caller row is admitted.'),indent=1)+'\n')
