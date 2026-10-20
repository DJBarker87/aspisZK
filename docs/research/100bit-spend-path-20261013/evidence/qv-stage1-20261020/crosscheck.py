"""Read-only cross-check of pinned counts; does not replay SBF or enumerate leaves."""
import hashlib,json,pathlib,subprocess
root=pathlib.Path.cwd(); base=root/'docs/research/100bit-spend-path-20261013'
def pin(p):
 p=root/p
 return {'path':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size_bytes':p.stat().st_size}
site_path='docs/research/100bit-spend-path-20261013/evidence/cu-bound3-20261020/sites.json'
sites=json.loads((root/site_path).read_text())
entry=next(x for x in sites['source_level_sites'] if x['id']=='S-BINARY-PARENT-SHA')
stage1=[r for r in entry['rows'] if r['role']=='stage1']
assert len(stage1)==2
for r in stage1:
 assert r['sha_calls']==595 and r['parent_hashes']==447
 assert r['fixed_nonparent_sha_calls']==148
 assert r['sha_calls']==r['parent_hashes']+115+30+3
 assert r['max_parent_hashes']==447
paths=[site_path,'crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/multiproof.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/transcript.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','docs/research/v8-r0-zk-20261009/lean/R1Z/EventsR1PBin.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/LayoutR1P3Bin.lean','docs/research/100bit-spend-path-20261013/design/WIRE-TX1-20261020.md','docs/research/100bit-spend-path-20261013/evidence/wire-tx1-20261020/source-inventory.json','docs/research/100bit-spend-path-20261013/evidence/proof-size-20261019/REPORT.md','docs/research/100bit-spend-path-20261013/lean/bridge-tx1-e5c186ba3-20261016/ExtractedTx1Model.lean','docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/ExtractedPreparedModel.lean']
report={'schema':'qv-stage1-count-crosscheck-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'measurement_revision':sites['target_revision'],'stage1_measured_rows':stage1,'stage2_comparison_only':[r for r in entry['rows'] if r['role']=='stage2'],'derivation':{'transcript':115,'leaf_calls':30,'full_tree_parent_cap':155,'folded_parent_cap':137,'parent_cap':447,'supplied_siblings_cap':420,'checkpoint':3,'stage1_call_cap':595,'distinct_first_read_cap':595},'pins':[pin(p) for p in paths],'status':'Counts agree with existing measurements. No new runtime execution or full source simulation.'}
(base/'evidence/qv-stage1-20261020/crosscheck.json').write_text(json.dumps(report,indent=2)+'\n')
print('Stage1 transfer/withdrawal: 595 = 115 + 30 + 447 + 3; distinct reads <= 595.')
