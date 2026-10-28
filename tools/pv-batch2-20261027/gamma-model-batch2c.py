"""Generalize the pinned numeric gamma continuation proof over its output carrier.
No native carrier/module substitution; this is an explicitly generic new theorem.
"""
from pathlib import Path
import subprocess,json,re,hashlib,sys
E=Path('evidence/pv-batch2-20261027/batch2c');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
j=json.loads((E/'GAMMA-IMPORT-SOURCE-PREFLIGHT.json').read_text());by={a['module']:a for a in j['project_modules']};parts=[];pins=[]
for name in ['GammaCallerDigitsModel','GammaCallerRankModel']:
 a=by[name];raw=subprocess.check_output(['git','show','research:'+a['resolution_path']],text=True);assert hashlib.sha256(raw.encode()).hexdigest()==a['source_sha256']
 body=raw.split('namespace AspisR1GammaCaller.DigitsModel\n',1)[1].rsplit('end AspisR1GammaCaller.DigitsModel',1)[0]
 body=re.sub(r'^#print axioms .*\n','',body,flags=re.M).replace('(ops : GammaHelpers)','(ops : GammaHelpers α)').replace('(out : field.WideExact)','(out : α)').replace('sampler.gamma_sample','sample').replace('dsimp only at h','try dsimp only at h').replace('simp only [if_true,bind_tc_ok,pure_bind] at h','try simp only [if_true,bind_tc_ok,pure_bind] at h')
 if name=='GammaCallerDigitsModel':
  a0=body.index('      try dsimp only at h')
  b0=body.index('      have hflat :',a0)
  body=body[:a0]+'''      change ((do
        let pair ← ops.add digits1 1#u32
        ok pair.2) >>= ops.decode) = .ok out at h
      with_unfolding_all simp only [bind_assoc_eq,bind_tc_ok] at h
'''+body[b0:]
 parts.append(body);pins.append(a)
header='''import Aeneas
import R1SourceSamplerByteRank
set_option autoImplicit false
namespace PV_B2_C_GammaNumeric
open Aeneas Aeneas.Std Result
variable {α : Type}
structure GammaHelpers (α : Type) where
  low : Array U8 32#usize → Result (Array U32 8#usize × U32)
  add : Array U32 8#usize → U32 → Result (Bool × Array U32 8#usize)
  decode : Array U32 8#usize → Result α

def sample (ops : GammaHelpers α) (block : Array U8 32#usize) : Result α := do
  let (digits,q) ← ops.low block
  let n ← q + 1#u32
  let (wrapped,ds1) ← ops.add digits n
  let ds2 ← if wrapped then do
    let (_,ds2) ← ops.add ds1 1#u32
    ok ds2
  else ok ds1
  ops.decode ds2
'''
s=header+''.join(parts)+''.join('#print axioms '+n+'\n' for n in ['bind_success','pair_bind_success','increment_value','gamma_digits_success','gamma_rank_success'])+'end PV_B2_C_GammaNumeric\n'
p=L/'PV_B2_C_GammaNumeric.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
r=dict(pinned_predecessors=pins,change='Output field carrier generalized to type parameter; control sequence unchanged; no whole-prover/native claim',output_sha256=hashlib.sha256(s.encode()).hexdigest())
p=E/'GAMMA-NUMERIC-PREFLIGHT.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==r
else:p.write_text(json.dumps(r,indent=2)+'\n')
