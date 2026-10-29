from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029');S=D.parent/'codex-pv-fscan-20261028/src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=S/'crates/aspis-r1-cost-probe/src/prover.rs';s=p.read_text();rows=[]
def bind(name,lo,hi,checks):
 text='\n'.join(s.splitlines()[lo-1:hi]);at=-1
 for c in checks:
  n=text.find(c,at+1);assert n>=0,(name,c);at=n
 rows.append(dict(name=name,path='crates/aspis-r1-cost-probe/src/prover.rs',span=[lo,hi],file_sha256=sha(p),body_sha256=hashlib.sha256(text.encode()).hexdigest(),ordered_checks=checks))
bind('audit_struct',106,115,['derive(Clone, Copy, Debug, PartialEq, Eq)','pub struct MaskedFixtureAudit','c1_columns_inactive_balanced: usize','mask_only_columns_inactive_balanced: usize','d_inactive_balanced: bool','g_inactive_balanced: bool','h1_padding_inactive_balanced: bool','h1_total_balanced: bool'])
bind('audit_return_guards',198,218,['let audit=audit_masks','audit.c1_columns_inactive_balanced!=16','audit.mask_only_columns_inactive_balanced!=10','!audit.d_inactive_balanced','!audit.g_inactive_balanced','!audit.h1_padding_inactive_balanced','return Err(Error::Semantic)','let h1_total_balanced=','if !h1_total_balanced { return Err(Error::Semantic); }','let audit=MaskedFixtureAudit{h1_total_balanced,..audit}','let proof=prove_from_semantics','Ok((proof,audit))'])
q=S/'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs';assert '"mask_audit":format!("{:?}",result.audit)' in q.read_text()
rows.append(dict(name='audit_format',path='tools/r1-cost-probe/src/bin/devnet_spend/plan.rs',span=[129,129],file_sha256=sha(q),operand='result.audit',law='audit_success_literal then audit_formatter_public',remaining='Debug derive/compiler V370; whole JSON and successful retry/native return association retained'))
# No panic payload inspection. Preserve the capture/control callsites precisely.
r=S/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';t=r.read_text();checks=['fn install_quiet_hook','std::panic::take_hook','std::panic::set_hook','pub fn p_r1_check','install_quiet_hook();','QUIET.with(|q| q.set(true))','std::panic::catch_unwind','public_data(ch)?','emit(&p)','convert(&p, &cert, &ln)?','extracted_builders','ck::check','QUIET.with(|q| q.set(false))']
pos=-1
for c in checks:
 n=t.find(c,pos+1);assert n>=0,c;pos=n
rows.append(dict(name='public_check_control',path=str(r.relative_to(S)),file_sha256=sha(r),span=[184,220],ordered_checks=checks,disposition='UNRESOLVED honest panic exclusion and call-stack/worker/TLS/joint-challenge law; suppression is not a privacy proof',source_binding_complete=False))
(D/'audit-source-binding.json').write_text(json.dumps(dict(rows=rows,evidence_class='own-1 local source guard/control association',compiler_boundary='V370 pending D381/D386',endpoint_removed=0,new_trust=0),indent=2)+'\n')
print('audit/control regions',len(rows),'audit value fixed on successful return; native observer instance remains open')
