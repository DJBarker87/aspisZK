"""Revalidate immutable NFP windows; compose only the concrete selected packet."""
from pathlib import Path
import sys,json,hashlib,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;P=E.parent/'slice-q-values-20261104'
sys.path.insert(0,str(P));import NFP_native_check as prior
from NFP_source_checks import body
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def check(native=None,frozen=None):
 expected=prior.check();report=json.loads((P/'NFP_NATIVE_VALIDATION.json').read_text()) if native is None else native
 need(report==expected,'native certificate/control/rename validation drift')
 ref=json.loads((P/'NFP_FROZEN_REF.json').read_text());path=R/ref['path'];need(sha(path)==ref['sha256'],'frozen input drift')
 f=json.loads(path.read_text()) if frozen is None else frozen
 query=body(f['crates/aspis-r1-cost-probe/src/candidate.rs'],'query_values')
 loop=body(f['crates/aspis-r1-cost-probe/src/candidate.rs'],'query_loop')
 need(hashlib.sha256(query.encode()).hexdigest()=='807182e869744ad952fca4dab9f46c42534c5259de5e0e5aff735edba8a9c649','query body changed')
 verifier=f['crates/aspis-r1-cost-probe/src/verifier.rs']
 need('struct QueryGeometry { start:usize, inverses:Vec<[M31;5]>, line_z:Vec<M31> }' in verifier,'node receiver type is not frozen M31')
 need('let z = geometry.line_z[i - geometry.start];' in query and 'let node = z.mul(z).double().sub(M31::ONE);' in query,'node source differs')
 need(len(re.findall(r'\.mul\(',query))==len(re.findall(r'\.double\(',query))==len(re.findall(r'\.sub\(',query))==1,'unregistered typed method use')
 intake=json.loads((P/'NFP_EDGE_INTAKE.json').read_text());alternatives=[]
 for edge in intake:
  target=edge['callee']
  if edge['caller'].endswith('query_values') and any(t in target for t in ['::CM31::double','::CM31::mul','::CM31::sub','::QM31::mul','::QM31::sub','::WideExact::mul','::WideExact::sub']):
   alternatives.append(dict(edge=edge['edge'],status='CLOSED under (ae)',kind='STATIC_UNREACHABLE',source_type='QueryGeometry.line_z:Vec<M31>; z:M31; native node operations M31::{mul,double,sub}',formal='AspisR1.NFS_PacketRoot.node; AspisR1.NFP_NodeDictionary.node',native='NFP_K020/022 with NFP_K021/023 controls and same-payload rename family',source_body_sha256=hashlib.sha256(query.encode()).hexdigest()))
 need(len(alternatives)==7,'typed inventory alternatives changed')
 return dict(status='PASS_INHERITED_NATIVE_SAME_BODY_ASSOCIATION',frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',native_report_ref=dict(path=str((P/'NFP_NATIVE_VALIDATION.json').relative_to(R)),sha256=sha(P/'NFP_NATIVE_VALIDATION.json')),positive_certificates=report['positives'],failing_controls=report['failing_controls'],rename_families=report['rename_families'],copy_patch_sha256=report['exact_KMX_patch_sha256'],query_body_sha256=hashlib.sha256(query.encode()).hexdigest(),loop_body_sha256=hashlib.sha256(loop.encode()).hexdigest(),typed_pruning=alternatives,new_Kani_runs=0,multiplication_in_Kani=False,quarantined=[],suspended=[],function_contracts_used=[],native_windows_rerun=False,qualification='Window certificates are paired here with NFS concrete caller/domain/trace/induction theorems and CLOSED callee packets; the old report remains local support on its own')
if __name__=='__main__':
 x=check();(E/'NFS_NATIVE_REUSE.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='typed_pruning'}))
