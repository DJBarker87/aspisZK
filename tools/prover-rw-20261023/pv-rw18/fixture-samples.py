"""Reify measured fixture samples; emit symbolic theorem applications only."""
from pathlib import Path
import json,sys,hashlib
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw18-20261026';log=e/'pv-rw18-fixtures-004/stdout.log'
rows=[json.loads(l) for l in log.read_text().splitlines() if l.startswith('{')]
assert [x['fixture'] for x in rows]==['transfer','withdrawal']
s='''import R1Z.ProverRw18ContextTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FixtureSamples
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
-- These are reified samples from the measured native fixture run, not a
-- supplied security-model interpretation or a proof-byte/audit comparison.
'''
for x in rows:
 n=x['fixture'];assert x['registry_links']==136 and x['comparisons']==816 and x['nonzero_tuples']>0 and x['full_output_and_final_power_equal']
 assert len(x['sample_values'])==16 and len(x['lambda'])==4
 numbers=','.join(str(v)+'#u32' for v in x['sample_values']);a,b,c,d=x['lambda']
 s+=f'''\ndef {n}_values : Array U32 16#usize := ⟨[{numbers}],by decide⟩
def {n}_tag : U32 := {x['sample_tag']}#u32
def {n}_lambda : Q := ⟨⟨{a}#u32,{b}#u32⟩,⟨{c}#u32,{d}#u32⟩⟩
'''
s+='\nvariable [ExternalTypes]\n'
for x in rows:
 n=x['fixture']
 s+=f'''
theorem {n}_context (ops : ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      {n}_tag (Array.to_slice {n}_values) {n}_lambda =
      PV_RW_CompressClosed.owned {n}_tag (Array.to_slice {n}_values) {n}_lambda :=
  ProverRw18ContextTotal.arity16 ops {n}_tag {n}_values {n}_lambda

theorem {n}_nonempty (ops : ExternalFuns) :
    ∃ out, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      {n}_tag (Array.to_slice {n}_values) {n}_lambda=ok out :=
  ProverRw18ContextTotal.total ops {n}_tag (Array.to_slice {n}_values) {n}_lambda
#print axioms {n}_context
#print axioms {n}_nonempty
'''
s+='end R1Z.ProverRw18FixtureSamples\n'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw18FixtureSamples.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
(e/'fixture-sample-map.json').write_text(json.dumps(dict(input_stdout_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),output_lean_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='Native sample reification plus symbolic model theorems. No security-model or original-source identity is inferred.',rows=rows),indent=2)+'\n')
