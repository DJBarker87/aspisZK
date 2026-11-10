import re
F=open('PCWR_E002_emitted/raw/PCWR_qs/Funs.lean').read()
blocks=re.split(r'\n(?=/--)',F)
def get(name):
    for b in blocks:
        if re.search(r'\ndef '+re.escape(name)+r'(?=\s)',b): return b.strip('\n')
    raise SystemExit('missing '+name)
fns=['aspis_core.field.P','aspis_core.field.CM31.new','sampler.qm31_div_pass_loop.body','sampler.qm31_div_pass_loop','sampler.qm31_div_pass','sampler.qm31_digits_loop0.body','sampler.qm31_digits_loop0','sampler.qm31_digits_loop1.body','sampler.qm31_digits_loop1','sampler.qm31_digits','sampler.qm31_sample']
body='\n\n'.join(get(n) for n in fns)
NS='AspisR1Qm31SamplerIndex';FR='PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1'
H=f'''-- PCWR_ item 4 (r1): AspisR1Qm31SamplerIndex.Funs, fresh = gate with NO external shim.
-- Fresh text: PCWR_E002 emission (original Aeneas 959659a6, overflow checks ON, frozen 4bb3b3f, cargo --jobs 4, CARGO_BUILD_JOBS=4, rustc -Zthreads 1,
-- identity by class receipt PCWE_E003), the PCQK_E015 root set with `--include aspis_core::field::P --include aspis_core::field::_::new`, so that
-- aspis_core::field::P and aspis_core::field::CM31::new are emitted frozen definitions (a U32 constant and `ok {{ a, b }}`), not externals.
-- The blocks below are copied verbatim from PCWR_E002_emitted/raw/PCWR_qs/Funs.lean (namespace changed; maxHeartbeats header dropped, default 200000 used).
-- The only binding left is the type alias of the three aspis_core field structures to the gate types (Types isomorphism is proved separately in PCQK/PCWM).
import Aeneas
import {NS}.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
noncomputable section

namespace {NS}
namespace {FR}
abbrev aspis_core.field.CM31 := {NS}.field.CM31
abbrev aspis_core.field.M31 := {NS}.field.M31
abbrev aspis_core.field.QM31 := {NS}.field.QM31

{body}

end {FR}
end {NS}

namespace PRVEq.{NS}.Funs_r1
open {NS}
'''
def thm(fresh,gate,tac):
    return f'''
set_option maxHeartbeats 200000 in
theorem {gate.replace('.','_')} : @{NS}.{FR}.{fresh} = @{NS}.{gate} := by
  {tac}
#print axioms {gate.replace('.','_')}
'''
T=H
T+=thm('aspis_core.field.P','field.P','first | rfl | (delta '+NS+'.'+FR+'.aspis_core.field.P '+NS+'.field.P; try rfl; done)')
T+=thm('aspis_core.field.CM31.new','field.CM31.new','first | rfl | (delta '+NS+'.'+FR+'.aspis_core.field.CM31.new '+NS+'.field.CM31.new; try rfl; done)')
deps={}
for n in fns[2:]:
    b=get(n).split(':=',1)[1] if ':=' in get(n) else get(n)
    b=get(n); b=b[b.index('\ndef '+n):]
    deps[n]=[m for m in fns[2:] if m!=n and re.search(r'(?<![A-Za-z0-9_.])'+re.escape(m)+r'(?![A-Za-z0-9_.])',b)]
for n in fns[2:]:
    rws=''.join(' (try rw [%s]);'%d.replace('.','_') for d in deps[n])
    if 'aspis_core.field.CM31.new' in get(n)[get(n).index('\ndef '+n):]: rws+=' (try rw [field_CM31_new]);'
    T+=thm(n,n,'first | rfl | (delta '+NS+'.'+FR+'.'+n+' '+NS+'.'+n+';'+rws+' try simp only [field_P]; try rfl; done)')
T+='\nend PRVEq.'+NS+'.Funs_r1\n'
open('PRVEq_AspisR1Qm31SamplerIndex_Funs_r1.lean','w').write(T)
