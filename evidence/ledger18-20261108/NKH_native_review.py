from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_bytes())
def raw(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():return lzma.decompress(Path(str(p)+'.xz').read_bytes())
 raise FileNotFoundError(p)
kmx=H((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes());rows=[];pairs=[];reused=[]
for folder,pre,table in [('verifier-weights-20261108','NJZ','NATIVE_PAIRS'),('sampler-transcript-20261108','NKD','NATIVE_MATRIX'),('terminal3-20261108','NJX','NATIVE_PAIRS')]:
 s=E.parent/folder;x=J(s/f'{pre}_{table}.json');ps=x if isinstance(x,list)else x['pairs'];own=[]
 for pair in ps:
  if isinstance(pair,list):pos,neg=pair[0]['attempt'],pair[1]['attempt']
  else:pos,neg=pair['positive'],pair['negative']
  if not pos.startswith(pre+'_'):
   reused.append(dict(provider=pre,positive=pos,negative=neg,validation_table=str((s/f'{pre}_{table}.json').relative_to(E.parents[1])),table_sha256=H((s/f'{pre}_{table}.json').read_bytes()),reviewed_first_install=pair.get('reviewed_first_install')if isinstance(pair,dict)else None));continue
  x=J(s/pos/'receipt.json');y=J(s/neg/'receipt.json');assert x['exit_status']==0 and y['exit_status']==1,(pos,neg)
  assert x['source_hashes']==y['source_hashes'],(pos,neg,'source')
  own.extend([pos,neg]);pairs.append(dict(positive=pos,negative=neg,identical_source_hashes=True))
 if pre=='NJZ':own+=['NJZ_K'+str(n).zfill(3)for n in list(range(27,33))+list(range(43,49))+list(range(51,57))]
 for a in sorted(set(own)):
  r=J(s/a/'receipt.json');gate=s/a/'sources'/f'{pre}_gate.py'
  gate_bytes=raw(gate)if gate.exists()or Path(str(gate)+'.xz').exists()else(s/f'{pre}_gate.py').read_bytes()
  assert b'KMX exact patch mismatch'in gate_bytes
  assert r['source_hashes'][pre+'_gate.py']==H(gate_bytes),a
  log=raw(s/a/'stdout.log').decode();assert ('VERIFICATION:- SUCCESSFUL'in log if r['exit_status']==0 else 'VERIFICATION:- FAILED'in log),a
  assert r['env']['CARGO_NET_OFFLINE']=='true'and str(r['swaps'])=='0'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  g=J(s/(a+'-graph-check.json'));lock=J(s/(a+'-lock-check.json'));assert g['graph_matches_frozen']and not g['edge_errors'],a
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  rows.append(dict(attempt=a,exit=r['exit_status'],semantic_verification_reached=True,module=r['module'],receipt_sha256=H((s/a/'receipt.json').read_bytes()),stdout_sha256=H(log.encode()),graph_sha256=H((s/(a+'-graph-check.json')).read_bytes()),lock_sha256=H((s/(a+'-lock-check.json')).read_bytes()),source_hashes=r['source_hashes'],all_crate_features=g.get('all_crate_features',g.get('all_features',g.get('features',g.get('selected_closure'))))))
# The exact reference patches and packet verification tables remain committed inputs.
inputs=[]
for folder,ns in [('verifier-weights-20261108',['NJZ_native.patch','NJZ_AH_TRANSCRIPTION.md','NJZ_PACKET_VERIFICATION.json','NJZ_STUBS.md']),('sampler-transcript-20261108',['NKD_NATIVE_REUSE.json','NKD_NATIVE_MATRIX.json','NKD_CERTIFICATES.md']),('terminal3-20261108',['NJX_NATIVE_PAIRS.json','NJX_ROOT_STATEMENTS.md','NJX_COHORT_FIX.json','NJX_AX2_DISAGREEMENT.json'])]:
 for n in ns:
  p=E.parent/folder/n;inputs.append(dict(path=str(p.relative_to(E.parents[1])),sha256=H(p.read_bytes())))
(E/'NKH_NATIVE_REVIEW.json').write_text(json.dumps(dict(status='PASS_READ_ONLY_RECEIPT_REVALIDATION',new_kani_runs=0,receipts=rows,pairs=pairs,inherited_pairs=reused,copy_patch_sha256=kmx,input_pins=inputs,quarantined_or_suspended_credit=[],excluded=['NJZ_K037 whole-table timeout','NJX_K021/022 failed unwinding calibration','all K2/K3 affected passes'],transport='P6/D188 option-A RECLASSIFICATION; runtime/crypto unchanged'),indent=1)+'\n')
print(json.dumps(dict(native_receipts=len(rows),direct_pairs=len(pairs),inherited_pair_tables=len(reused))))
