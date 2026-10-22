#!/usr/bin/env python3
"""Abstract only verified next_word call sites in the retained extraction.
This is a generated proof-cut schedule, not a new Rust extraction certificate.
"""
from pathlib import Path
import re,hashlib,json
E=Path(__file__).resolve().parent.parent
P=Path('docs/research/v8-r0-zk-20261009/lean')
raw=(P/'AspisR1ProverStreams/Funs.lean').read_text()
old=(E/'shipped-scalar-excluded.lean.txt').read_text()
s='''import R1Z.ProverCommitCallerLoop
/-! Fixed scalar schedules after abstraction of the verified next-word call.
Generated from AspisR1ProverStreams; see the literal source receipts.
No claim that this abstraction alone identifies the whole shipped caller. -/
set_option autoImplicit false
namespace R1Z.ProverCommitShippedSchedule
open Aeneas Aeneas.Std Result ControlFlow AspisR1ProverCaller7
variable {State : Type} (nextWord : State → Result (U32 × State))
abbrev Sample := core.result.Result aspis_core.field.M31
  state_only_hiding.StateOnlyMaskBuildError
'''
a=old.index('theorem usize_more');b=old.index('\nabbrev Sample',a)
s+=old[a:b].replace('core.iter.range.IScalarStep','core.iter.range.UScalarStep').replace('  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,','  have hlt : attempts.val < UScalar.max .Usize := by scalar_tac\n  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,',1).replace('forward_checked, hmax]', 'forward_checked, hlt]')
rows=[]
for family,cls,typ in [('mask','state_only_hiding.SeedExpander','Usize'),('source','state_only_entropy.Profile21SourceExpander','I32')]:
 a=raw.index('def '+cls+'.m31_loop.body');b=raw.index('/--',raw.index('def '+cls+'.m31\n',a)) if family=='mask' else raw.index('/--',raw.index('def '+cls+'.m31\n',a))
 # Last source m31 is followed by mask-domain declarations.
 block=raw[a:b]
 block=re.sub(r'/--.*?-/', '', block, flags=re.S)
 block=block.replace('@[rust_loop]','').replace(cls+'.next_word self','nextWord self')
 block=block.replace(cls+'.m31_loop.body','body').replace(cls+'.m31_loop','run').replace(cls+'.m31','scalar').replace(cls,'State')
 block=block.replace('def body\n','def body (nextWord : State → Result (U32 × State))\n').replace('def run\n','def run (nextWord : State → Result (U32 × State))\n').replace('def scalar\n','def scalar (nextWord : State → Result (U32 × State))\n')
 block=block.replace('body iter1 self1','body nextWord iter1 self1').replace('run\n      {','run nextWord\n      {')
 block=block.replace('state_only_hiding.MASK_SAMPLE_RETRY_LIMIT','16#usize').replace('body iter1','body nextWord iter1').replace('let i1 ← aspis_core.field.P','let i1 := aspis_core.field.P')
 s+=f'\nnamespace {family}\n'+block
 a=old.index(f'namespace {family}');b=old.index(f'end {family}',a)
 proofs=old[a:b]
 proofs=proofs[proofs.index('def finite'):]
 proofs=proofs.replace('def finite :','def finite (nextWord : State → Result (U32 × State)) :').replace(cls+'.next_word state','nextWord state')
 proofs=proofs.replace('finite n after','finite nextWord n after').replace('finite n state','finite nextWord n state').replace('finite 16 state','finite nextWord 16 state')
 proofs=proofs.replace(cls+'.m31_loop.body','body').replace(cls+'.m31_loop','run').replace(cls+'.m31','scalar')
 proofs=proofs.replace('run\n      {','run nextWord\n      {').replace('scalar state','scalar nextWord state')
 proofs=proofs.replace('rw [run, loop]','rw [run, loop]').replace('loop_finite 16 state','loop_finite nextWord 16 state')
 proofs=proofs.replace('      scalar', '      scalar')
 proofs=proofs.replace('  rw [state_only_hiding.MASK_SAMPLE_RETRY_LIMIT]\n','')
 s+=proofs.replace('let p ← aspis_core.field.P','let p := aspis_core.field.P')+f'end {family}\n'
 rows.append(dict(family=family,input_sha256=hashlib.sha256(raw.encode()).hexdigest(),abstracted_call=cls+'.next_word',iterator=typ))
s+='\n#print axioms usize_more\n#print axioms usize_done\nend R1Z.ProverCommitShippedSchedule\n'
(P/'R1Z/ProverCommitShippedSchedule.lean').write_text(s)
(E/'schedule-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
