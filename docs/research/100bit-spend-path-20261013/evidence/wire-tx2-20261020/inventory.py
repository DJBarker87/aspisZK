from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[5]; base=root/'docs/research/100bit-spend-path-20261013'; ev=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=base/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
s=f.read_text(); declarations=[]
for m in re.finditer(r'^def ([^\s]+)',s,re.M):
 z=s.find('\n/--',m.end()); z=len(s) if z<0 else z
 declarations.append((m.group(1),m.start(),z))
sites=[]
for m in re.finditer(r'aspis_coredigestDigest32Inst\.digest|aspis_core\.state_only_private_merkle\.private_leaf_hash_with_digest|aspis_core\.r0\.merkle\.parent_with_digest',s):
 owner=next(n for n,a,z in declarations if a<=m.start()<z)
 sites.append(dict(owner=owner,line=s.count('\n',0,m.start())+1,operation=m.group(),scope='excluded-eight-way' if 'r0.merkle.parent' in m.group() else 'included'))
metadata={
  621: ('leafC1', 514, '0x10,0x71', 'q[..480] + q[608..640]', 'batch_leaf_typed; LeafDigestLaw; tag operation'),
  634: ('leafSmall', 162, '0x10,0xf1', 'q[480..608] + q[640..672]', 'batch_leaf_typed; LeafDigestLaw; tag operation'),
  646: ('leafSmall', 162, '0x10,0x72', 'q[672..800] + q[800..832]', 'batch_leaf_typed; LeafDigestLaw'),
  688: ('binaryNode', 65, '0x12', 'current[32] + sibling[32]', 'sibling_read_typed; get/add success'),
  695: ('binaryNode', 65, '0x12', 'sibling[32] + current[32]', 'sibling_read_typed; get/add success'),
  713: ('binaryNode', 65, '0x12', 'occupied left[32] + occupied right[32]', 'occupied_typed'),
  1096: ('excluded-generic-eight-way', 257, '0x18', 'eight children[32]', 'adopted batch supplies Arity::Two'),
  2613: ('binding.compactProof', 57607, 'no added prefix; stored proof magic R1P3CB18', 'whole proof singleton', 'resume_typed; caller proof width'),
  2625: ('binding.asf8Account', 1880, 'no added prefix; ASF8 envelope', 'supplied public singleton', 'resume_typed; admitted serializer width'),
  2649: ('binding.checkpointChecksum', 1758, 'UNPROVED:R1:checkpoint', 'domain[22] + bytes[..len-32][1736]', 'resume_typed; S2 checkpoint width')}
for site in sites:
 c,n,t,construction,dep=metadata[site['line']]
 site.update(record_class=c,length=n,tag=t,construction=construction,dependency=dep)
assert len([x for x in sites if x['operation'].endswith('.digest')])==6
assert len([x for x in sites if 'private_leaf' in x['operation']])==3
# Retain the exact emitted helper definitions, with no operation substitutions.
a=s.index('@[global_simps, irreducible] def multiproof.BINARY_NODE_TAG');z=s.index('/-- [aspis_r1_cost_probe::multiproof::root_matches]',a)
body=(base/'lean/WireTx2BinaryBodies.lean').read_text();assert s[a:z] in body
a=s.index('def verifier.candidate.batch_leaf\n');z=s.index('/-- [aspis_r1_cost_probe::verifier::candidate::same_batch_leaf]',a)
leaf=s[a:z].replace('def verifier.candidate.batch_leaf','def verifier.candidate.batch_leafWithWireOps').replace('  {H : Type}', '  (ops : LeafOps)\n  {H : Type}').replace('aspis_core.r0.merkle.C1_TAG','ops.c1Tag').replace('aspis_core.r0.merkle.C2_TAG','ops.c2Tag').replace('aspis_core.state_only_private_merkle.private_leaf_hash_with_digest\n      aspis_coredigestDigest32Inst hash','ops.leaf\n      aspis_coredigestDigest32Inst hash')
salt_conversion = "    let r ←\n      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s\n    let salt ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r"
assert leaf.count(salt_conversion)==3
leaf=leaf.replace(salt_conversion, "    let salt ← ops.salt s")
assert leaf in (base/'lean/WireTx2LeafBodies.lean').read_text()
finish=s[s.index('def verifier.finish_relation\n'):s.index('\n/--',s.index('def verifier.finish_relation\n'))]
assert not any(x in finish for x in ['Digest32','digest','hash'])
# Existing explicit-operation resume adapter is the retained complete body;
# its original binding checker remains in the stage2 packet (not rerun here).
paths=[f,base/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Types.lean',base/'lean/Stage2ContinuationResumeBody.lean',root/'crates/aspis-r1-cost-probe/src/candidate.rs',root/'crates/aspis-r1-cost-probe/src/verifier.rs',root/'crates/aspis-r1-cost-probe/src/multiproof.rs',root/'crates/aspis-core/src/state_only_private_merkle.rs',root/'crates/aspis-core/src/r0/merkle.rs',base/'evidence/freeze-20261020/llbc-comparison.json',root/'programs/r1-cost-probe/src/r1_pool_adapter.rs']
data=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=[dict(path=str(p.relative_to(root)),sha256=sha(p),size=p.stat().st_size) for p in paths],sites=sites,binary_helpers_exact=True,leaf_adapter_exact_modulo_named_operations_and_salt_conversion=True,finish_relation_has_no_hash_parameter_or_call=True,new_classes=[],exclusions=['generic eight-way parent branch; adopted batch fixes Arity::Two','arbitrary observer/backend callback effects are outside the Digest32 inventory'])
(ev/'source-inventory.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(dict(sites=sites,binary_helpers_exact=True),indent=2))
