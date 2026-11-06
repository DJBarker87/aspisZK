from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;source='NJR_src/crates/aspis-r1-cost-probe/src/NJR_parent.rs';sha=hashlib.sha256((E/'NJR_parent.rs.txt').read_bytes()).hexdigest()
spec=[('M03','pending_destination',39,[40,41],'NJR_Cuts.pending','raw64, arbitrary selected weight window and actual destination index<64'),('M04','query_weights',46,[47,48],'NJR_Cuts.queryReturn','complete owned weights64 plus all-field query Result'),('M04','query_raw',30,[31,52],'NJR_Cuts.queryReturn','complete owned raw64 plus all-field query Result'),('M04','query_scalars',32,[33,34,35,36,53],'NJR_Cuts.queryReturn','full rhs8/power4/next/terms and every Error variant'),('M05','flush_receiver_window',37,[38,54,55],'NJR_Cuts.flushStep','full immutable raw64 receiver/index and selected arbitrary mutable K slot'),('M05','flush_destination_window',49,[50,51],'NJR_Cuts.flushStep','one actual arbitrary64-vector enumerate/iter_mut step, destination and full frame'),('M09','reader_backing',42,[43,44,45],'NJR_ReaderCut.Cut','SAME1768 backing/window, input cursor, full Reader reply/post, owned Err/drop event and successful64-vector frame')]
rows=[]
for member,harness,pos,controls,cut,domain in spec:
 refs=[]
 for num in [pos]+controls:
  a=f'NJR_K{num:03d}';r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text();positive=num==pos
  assert r['exit_status']==(0 if positive else 1),(a,'exit')
  assert ('VERIFICATION:- SUCCESSFUL' if positive else 'VERIFICATION:- FAILED') in log,a
  assert 'timed out' not in log and 'unwinding assertion' not in log,a
  assert r['source_hashes'][source]==sha,(a,'source')
  graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());check=json.loads((E/(a+'-source-check.json')).read_text())
  assert graph['graph_matches_frozen'] and lock['unchanged'] and not check['errors'],a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_TARGET_DIR'].endswith('/NJR_target'),a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert str(r['swaps'])=='0',a
  refs.append(dict(attempt=a,role='PASS' if positive else 'matched semantic FAIL',receipt=a+'/receipt.json',graph=a+'-graph-check.json',lock=a+'-lock-check.json',source_sha256=sha,**{k:r[k] for k in ['source_revision','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes']}))
 rows.append(dict(member=member,harness='verifier::NJR_parent::'+harness,typed_cut=cut,domain=domain,source=source,source_sha256=sha,positive=refs[0],controls=refs[1:]))
(E/'NJR_NATIVE_CERTIFICATES.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',status='reviewed parent-cut components, not a composed TX2:065 root',transport='option-A P6/D188 reclassification, not removal',kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',rows=rows,excluded={'compile_setup':['NJR_K001','NJR_K002','NJR_K003'],'timeouts':['NJR_K011','NJR_K025','NJR_K029']}),indent=2)+'\n')
print(json.dumps(dict(selected_positive_cuts=len(rows),matched_controls=sum(len(r['controls']) for r in rows),source_sha256=sha)))
