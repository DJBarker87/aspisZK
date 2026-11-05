"""Read-only revalidation of the exact retained cuts selected by NHS.
No solver, source-validator mutation, or promotion of predecessor driver rows.
"""
from pathlib import Path
import hashlib,json,subprocess,re
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
pins={}
def read(p):
 p=Path(p);p=p if p.is_absolute()else R/p
 b=p.read_bytes();pins[str(p.relative_to(R))]=H(b);return b
def J(p):return json.loads(read(p))
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
pairs=[]
def pair(directory,positive,negative):
 d=R/'evidence'/directory;rs=[]
 for a,status in [(positive,0),(negative,1)]:
  r=J(d/a/'receipt.json');rs.append(r);log=read(d/a/'stdout.log').decode()
  assert r['exit_status']==status and r['limits']==LIMITS and int(r['swaps'])==0,a
  assert 'VERIFICATION:- '+('FAILED'if status else'SUCCESSFUL')in log,a
  assert 'timed out'not in log.lower()and 'unwinding assertion'not in log.lower(),a
  if status:assert re.search(r'\*\* 1 of \d+ failed',log),a
  g=J(d/(a+'-graph-check.json'));lock=J(d/(a+'-lock-check.json'));src=J(d/(a+'-source-check.json'))
  assert g['graph_matches_frozen'] and lock['unchanged']and lock['before']==lock['after']==LOCK
  assert src['errors']==[] and r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert J(d/(a+'-admission.json'))['reservation']['allowed']is True
  assert J(d/(a+'-admission.json'))['exit']==0
  for n,h in r['source_hashes'].items():assert H(read(d/a/'sources'/n))==h,(a,n)
 if (positive,negative)==('NFW_K099','NFW_K100'):
  assert rs[0]['module']=='verifier::NFW_prepared::copy_folded' and rs[1]['module']==rs[0]['module']+'_wrong'
 elif (positive,negative)==('NGC_K038','NGC_K039'):
  assert rs[0]['module']=='verifier::NGC_windows::checkpoint_copy_positive' and rs[1]['module']=='verifier::NGC_windows::checkpoint_copy_negative'
 else:assert rs[0]['module']==rs[1]['module'],(positive,negative)
 assert {n:h for n,h in rs[0]['source_hashes'].items()if n.endswith('.rs')}=={n:h for n,h in rs[1]['source_hashes'].items()if n.endswith('.rs')}
 pairs.append(dict(directory=directory,positive=positive,control=negative,module=rs[0]['module']))
def build():
 for p in [12,16,18,20,22,24]:pair('slice-d-prepared-20261105',f'NGN_K{p:03}',f'NGN_K{p+1:03}')
 for n in [30,31]:pair('slice-d-prepared-20261105','NGN_K029',f'NGN_K{n:03}')
 for p in [11,31,65,69,99]:pair('slice-d-prepare-20261104',f'NFW_K{p:03}',f'NFW_K{p+1:03}')
 for p in [36,38,40]:pair('slice-d-checkpoint-20261104',f'NGC_K{p:03}',f'NGC_K{p+1:03}')
 # Closed child packets are retained, not recreated by local native-cut passes.
 for d,ns in {
 'slice-d-prepared-20261105':['NGN_FRAME.md','NGN_STUBS.md','NGN_NATIVE_PAIRS.json','NGN_REUSE.json','NGN_EmittedEq.lean','NGN_FrameChain.lean'],
 'prepare-emit-20261106':['NHL_HYPOTHESES.md','NHL_PreparedRecompose.lean','NHL_QueryInterface.lean','NHL_AUDIT.json','NHL_REMAINING.md'],
 'transcript-queries3-20261106':['NHK_CLOSED.json','NHK_EDGES.json','NHK_AUDIT.json','NHK_ASSOCIATION.md','NHK_TRACE.md','NHK_certificate.py','NHK_REVALIDATED_REUSE.json'],
 'transcript-scalars-20261105':['NGT_CLOSED.json','NGT_AUDIT.json','NGT_BRIDGES.md','NGT_CallerInterface.lean'],
 'prepared-claim2-20261105':['NGY_CLOSED.json','NGY_AUDIT.json','NGY_EDGES.json','NGY_NATIVE_MATRIX.json'],
 'prepared-claim-20261105':['NGU_CLOSED.json','NGU_AUDIT.json','NGU_PreparedClaim.lean'],
 'slice-d-checkpoint-20261104':['NGC_CLOSED.json','NGC_AUDIT.json','NGC_EDGES.json','NGC_CERTIFICATES.json','NGC_REMAINING.md','NGC_PreparationBoundary.lean','NGC_PrestateBridge.lean','NGC_KNE_Writer.lean','NGC_InitialInvariant.lean','NGC_CheckpointBridge.lean','NGC_certify.py'],
 'slice-d-prepare-20261104':['NFW_Transcript.lean','NFW_PreparedFields.lean','NFW_PREPARED_NATIVE_SOURCE.json','LPh_STUBS.md']}.items():
  for n in ns:read('evidence/'+d+'/'+n)
 # Preserve the predecessor's own nested immutable input manifest.
 for p,h in J('evidence/slice-d-prepared-20261105/NGN_REUSE.json').items():assert H(read(p))==h,p
 assert J('evidence/transcript-queries3-20261106/NHK_REVALIDATED_REUSE.json')['status']=='PASS'
 assert J('evidence/transcript-queries3-20261106/NHK_CLOSED.json')['row']=='TX1:168'
 assert J('evidence/prepared-claim2-20261105/NGY_CLOSED.json')['row']=='TX1:193'
 out=dict(status='PASS',pairs=len(pairs),selected_pairs=pairs,inputs=pins,new_tool_attempts=0,method='same frozen native receipt/log/source/graph/lock/feature/admission checks; pinned child composition and ax2 certificates; no unchanged prover rerun')
 (E/'NHS_REVALIDATED_REUSE.json').write_text(json.dumps(out,indent=1)+'\n')
 print(json.dumps(dict(status='PASS',pairs=len(pairs),inputs=len(pins))))
if __name__=='__main__':build()
