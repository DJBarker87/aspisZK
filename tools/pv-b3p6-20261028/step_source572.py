"""Actual Usize range source-state maps, with complete-body template checks.
Early returns, callback errors and unwinds can remove an event. They cannot
add an execution of the sole checked increment outside its strict-order gate.
"""
from pathlib import Path
import argparse,json,hashlib,re
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()
TEMPLATES=[
'''default fn spec_next(&mut self) -> Option<A> {
 if self.start < self.end {
 let n = Step::forward_checked(self.start.clone(), 1).expect("`Step` invariants not upheld");
 Some(mem::replace(&mut self.start, n))
 } else { None }
}''',
'''default fn spec_next(&mut self) -> Option<A> {
 if self.is_empty() { return None; }
 let is_iterating = self.start < self.end;
 Some(if is_iterating {
 let n = Step::forward_checked(self.start.clone(), 1).expect("`Step` invariants not upheld");
 mem::replace(&mut self.start, n)
 } else { self.exhausted = true; self.start.clone() })
}''',
'''default fn spec_try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
 where Self: Sized, F: FnMut(B, A) -> R, R: Try<Output = B>, {
 if self.is_empty() { return try { init }; }
 let mut accum = init;
 while self.start < self.end {
 let n = Step::forward_checked(self.start.clone(), 1).expect("`Step` invariants not upheld");
 let n = mem::replace(&mut self.start, n);
 accum = f(accum, n)?;
 }
 self.exhausted = true;
 if self.start == self.end { accum = f(accum, self.start.clone())?; }
 try { accum }
}''']
def tokens(s):return re.findall(r'"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',s)
def check(body,index):assert tokens(body)==tokens(TEMPLATES[index]),index

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 inv=json.loads((R/'FORMATTING-EVENTS-D569.json').read_text());g=json.loads((I/'direct3-instantiated-callcone.json').read_text());matches=[]
 for j,row in enumerate(inv['range_source_parity']):
  check(row['deployed_body'],j);check(row['extractor_body'],j)
 controls={}
 for name,change in {'non_strict_guard':lambda s:s.replace('self.start < self.end','self.start <= self.end'), 'intervening_write':lambda s:s.replace('let n =','self.start = self.end; let n ='), 'wrong_step':lambda s:s.replace('clone(), 1','clone(), 2')}.items():
  for j,t in enumerate(TEMPLATES):
   try:check(change(t),j)
   except AssertionError:pass
   else:raise AssertionError((name,j))
  controls[name]='all three templates rejected'
 s='''import PV_B3P_StepSource572227
namespace PV_B3P_StepFamily572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
'''
 for fid,suffix,carrier in [(186,'range','core.ops.range.Range Usize'),(337,'inclusive_next','core.ops.range.RangeInclusive Usize'),(217,'inclusive_fold','core.ops.range.RangeInclusive Usize')]:
  pairs=[(k,v)for k,v in g['instances'].items()if v['id']==fid];assert len(pairs)==1
  key,v=pairs[0];assert v['environment']['types'][0]=={'Literal':{'UInt':'Usize'}}
  events=[e for e in inv['events']if e['instance']==key and e['detail'].get('name','').endswith('::expect_failed')];assert len(events)==1
  edges=[e for e in g['edges']if e['caller']==key];forward=[e for e in edges if e['callee_name'].endswith('::forward_checked')];assert len(forward)==1
  target=g['instances'][forward[0]['callee']];assert target['environment']['types']==[] # resolved StepUsize implementation
  matches.append(dict(instance=key,environment=v['environment'],statement=events[0]['statement'],checked_successor=forward[0],source_state_projection='current self.start, current self.end; before mem::replace and callback',lemma=f'PV_B3P_StepFamily572227.{suffix}_certificate'))
  s+=f'''/-- Exact source instance {key}; observe current fields at the guarded call. -/
def {suffix}_state (r : {carrier}) : Result (Option (Option Usize)) :=
  PV_B3P_StepSource572227.event r.start r.end

theorem {suffix}_guard (r : {carrier}) (answer : Option Usize)
    (observed : {suffix}_state r = .ok (some answer)) : optionGuard answer :=
  PV_B3P_StepSource572227.event_guard r.start r.end answer observed

theorem {suffix}_certificate {{α : Type}} (r : {carrier}) (answer : Option Usize)
    (observed : {suffix}_state r = .ok (some answer))
    (normal first second : Result α) :
    ¬ diagnostic (optionGuard answer) ∧
      branch (optionGuard answer) normal first = branch (optionGuard answer) normal second :=
  PV_B3P_StepSource572227.event_certificate r.start r.end answer observed normal first second
#print axioms {suffix}_guard
#print axioms {suffix}_certificate
'''
 s+='end PV_B3P_StepFamily572227\n'
 meta=dict(instances=matches,negative_controls=controls,source_inventory_sha256=sha((R/'FORMATTING-EVENTS-D569.json').read_bytes()),graph_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),generic_sha256=sha((D/'lean/PV_B3P_StepSource572227.lean').read_bytes()),generated_sha256=sha(s.encode()),evidence_class='script-checked source control/state projection plus Lean successor guard proof',local_expect_sites=3,full_iterator_borrow_drop_caller_association=False,whole_source_cone_complete=False,premises_removed=[])
 for p,text in {D/'lean/PV_B3P_StepFamily572227.lean':s,R/'STEP-SOURCE-GUARDS-D572.json':json.dumps(meta,indent=2)+'\n'}.items():
  if args.check:assert p.read_text()==text,p
  else:p.write_text(text)
 print(json.dumps(dict(expect_source_maps=3,controls=controls,check=args.check)))
if __name__=='__main__':main()
