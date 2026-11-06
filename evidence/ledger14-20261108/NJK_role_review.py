from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent
p=E/'NJK_CANDIDATE_REVIEW.json';review=json.loads(p.read_text());out=[]
roles={
'AspisR1.NJF_Root.finish':('positive capsule','data; allocator realization r; explicitly retained SAME-call Domain; reviewed actual PairPort Cut'),
'AspisR1.NJF_FinishObserved.source':('internal producer','retained Domain; produces complete source invocation, all child clauses and SAME pair Bound internally'),
'AspisR1.NJF_FinishInstantiation.root':('positive result-only capsule','data; allocator realization r; retained SAME-call Domain; no arbitrary Ops'),
'AspisR1.NJF_PairInstantiation.source':('internal pair source lemma','primitive pair domain; derived by NIT_PairDomain.caller at SAME actual NEW return inside positive capsule, never retained at deployed root'),
'AspisR1.NIX_Cuts.sampler_compose':('native cut consumer','data and reviewed samplerCut; sample/map/fallback child clauses are supplied by sampler_replies, which calls unconditional packet/deployed fallback; none retained as hypothesis'),
'AspisR1.NIX_Cuts.sampler_replies':('positive child-reply producer','only SAME block and row; derives every callee equation and canonical domain'),
'AspisR1.NIX_SamplerLaw.adopted':('positive adopted-source producer','only SAME block and adopted CircleRow; no dictionary, output, success or Run hypothesis'),
'AspisR1.NIX_ValidatedCut.source':('REJECTED generic source identity','arbitrary B Boundaries; not in positive-root inventory (au)(5); no native dispatch cut consumed'),
'AspisR1.NIX_DispatchRun.first':('internal generic bind decomposition','arbitrary B and digest D; source helper only, does not supply positive native cut composition'),
'AspisR1.NIX_DispatchRun.second':('internal generic bind decomposition','arbitrary B and digest D; source helper only, does not supply positive native cut composition'),
'AspisR1.NIX_DispatchRun.returned':('internal generic continuation','B.circle block row=ok point is a child endpoint clause; circle_packet installs F3M sampler but candidate has no final theorem applying it in the complete native dispatch'),
'AspisR1.NIX_DispatchRun.rejected':('internal error continuation','arbitrary B is unused on Err; no native positive result/frame composition'),
'AspisR1.NIX_DispatchRun.abort_prefix':('generic abort-prefix law','arbitrary continuations; independent helper, no native parent invocation supplied'),
'AspisR1.NIX_DispatchCut.predecessor_domain':('caller-domain producer','SAME parsed prefix success is retained genuine caller provenance; proves framed length, not native parent Result'),
'AspisR1.NIX_ProducerInstall.framed':('caller provenance producer','SAME parser bytes/prefix success and row<27 establish actual token/row/frame; no full parent transport'),
'AspisR1.NIX_ResidualLog.packet':('positive child producer','only original canonical SAME row/helper/chi domain; derives reads/Law/Domain/complete source reply internally'),
'AspisR1.NIX_ResidualCut.packet':('positive native cut consumer','original canonical SAME row/helper/chi domain; existential replies produced internally; only reviewed K058/K059 cut on those replies retained'),
'AspisR1.NJH_Observer.emitted':('positive leaf under explicit (as)(3)','unused Ops binder only; canonical body never reads an op. (at)(2) provenance checked separately; no arbitrary dictionary relied upon'),
}
for row in review['rows']:
 for r in row['roots']:
  n=r['root'];assert n in roles,n
  role,h=roles[n];out.append(dict(row=row['row'],root=n,owner_module=r['owner_module'],statement_sha256=r['statement_sha256'],role=role,complete_hypothesis_disposition=h,admissible_as_standalone_positive_root=role.startswith('positive'),complete_statement_location='NJK_CANDIDATE_REVIEW.json'))
(E/'NJK_HYPOTHESIS_INVENTORY.json').write_text(json.dumps(dict(rule='(aq)(2); internal child clauses must be discharged by packet, never retained positive-root premises',roots=out),indent=1)+'\n')
# Retain full native-source/copy/control domains, not verdict-only certificates.
checks=[]
for folder,pre in [('slice-d-pair8-20261107','NJF'),('verify-observed5-20261107','NIX')]:
 packet=json.loads((E.parent/folder/f'{pre}_CLOSED.json').read_text())
 for f in packet['functions']:
  for pos,neg in f['native_pairs']:
   d=E.parent/folder;rp=json.loads((d/pos/'receipt.json').read_text());rn=json.loads((d/neg/'receipt.json').read_text());assert rp['exit_status']==0 and rn['exit_status']!=0
   for name in [pos,neg]:
    q=d/name/'stdout.log';raw=q.read_bytes()if q.exists()else lzma.decompress(Path(str(q)+'.xz').read_bytes());s=raw.decode();assert 'CBMC timed out'not in s and 'VERIFICATION:- '+('SUCCESSFUL'if name==pos else'FAILED')in s
   checks.append(dict(rows=f['rows'],positive=pos,negative=neg,positive_receipt_sha256=hashlib.sha256((d/pos/'receipt.json').read_bytes()).hexdigest(),negative_receipt_sha256=hashlib.sha256((d/neg/'receipt.json').read_bytes()).hexdigest(),reviewed_by='NJK_'+pre+'_REVALIDATION.json',credit='candidate-specific only; subject to NJK full semantic and raw gates'))
(E/'NJK_NATIVE_PACKET_REVIEW.json').write_text(json.dumps(dict(status='PASS_READONLY_RECEIPTS_NO_NEW_KANI',pairs=checks,KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',new_kani=0,field_multiplication='Lean-discharged logs only',Option_fn='No new pointer-dependent native credit; observer Lean-only (as)(3)'),indent=1)+'\n')
print('NJK root roles, hypothesis inventory and native packet controls sealed')
