"""Exact source-prefix erasure and operand-order check; never edits frozen source."""
from pathlib import Path
import subprocess,json,hashlib,sys
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(E.parent/'slice-q-fnptr-20261029'))
from NEF_OBSERVER_CERTIFICATE import tok
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
path='crates/aspis-r1-cost-probe/src/verifier.rs'
def check(helper):
 frozen=subprocess.check_output(['git','show',REV+':'+path],cwd=R,text=True)
 start=frozen.index('            let u=query as usize;',frozen.index('fn for_range('))
 end=frozen.index('            flat.extend_from_slice(&values);',start)
 prefix=frozen[start:end]
 hstart=helper.index(' let u=query as usize;',helper.index('fn NEO_gather_values('))
 hend=helper.index(' let mut log=',hstart);actual=helper[hstart:hend]
 transforms=[(' let left=u/4*4;\n',''),('FibreIndex::new(left)','FibreIndex::new(u/4*4)'),(' let right=u/4*4+3;\n',''),('FibreIndex::new(right)','FibreIndex::new(u/4*4+3)'),('let square=line_x.mul(line_x);let doubled=square.double();let line_z=doubled.sub(M31::ONE);','let line_z=line_x.mul(line_x).double().sub(M31::ONE);')]
 for old,new in transforms:
  assert actual.count(old)==1,('missing/duplicate ANF substitution',old)
  actual=actual.replace(old,new)
 assert tok(prefix)==tok(actual),'native helper differs from exact frozen prefix'
 tail=helper[hend:helper.index('\n#[kani::proof]',hend)]
 want='''let mut log=NEO_RowLog{query,u,left,right,px:circle_x,py:circle_y,lx:line_x,ly:line_y,square,doubled,z:line_z};
 #[cfg(NEO_wrong_geometry)] {log.left=left+1;}
 Ok((values,log))
}'''
 assert tok(tail)==tok(want),'ghost/local result/order changed'
 assert not any(x in helper for x in ['static mut','Option<fn','stub_verified','proof_for_contract'])
 for annotation in ['#[kani::stub(crate::fast_domain::fibre_point,NEO_point)]','#[kani::stub(crate::fast_domain::line_node,NEO_line)]','#[kani::stub(M31::mul,NEO_product)]']:
  assert helper.count(annotation)==1
 return dict(frozen_revision=REV,source_file=path,frozen_prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),exact_prefix_after_local_ANF_erasure=True,order=['checked fibre index','fibre point','aligned left checked index','left line node','aligned right checked index','right line node','square','double','subtract ONE','five-cell zero test'],prefix_state='local values only; Vec append and push are excluded and remain OPEN',native_root_status='OPEN; this certificate is only the gather prefix',rule16='local returned record; no static or pointer log')
if __name__=='__main__':
 s=(E/'NEO_geometry.rs.txt').read_text();result=check(s);tests=[]
 for label,old,new in [('left input','FibreIndex::new(left)','FibreIndex::new(right)'),('right input','let right=u/4*4+3;','let right=u/4*4+2;'),('product receiver','line_x.mul(line_x)','line_y.mul(line_x)'),('zero rejection','return Err(Error::Query);','return Err(Error::Parse);'),('ghost source','px:circle_x','px:circle_y')]:
  assert old in s
  try:check(s.replace(old,new,1))
  except AssertionError:tests.append(dict(test=label,rejected=True))
  else:raise AssertionError('mutation accepted: '+label)
 (E/'NEO_GEOMETRY_SOURCE.json').write_text(json.dumps(dict(certificate=result,mutations=tests),indent=1)+'\n');print(json.dumps(dict(positive=True,mutations_rejected=len(tests))))
