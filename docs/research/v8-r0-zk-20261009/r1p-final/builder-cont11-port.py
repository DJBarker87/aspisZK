#!/usr/bin/env python3
"""Deterministic ABI port, retaining source externals as instance parameters.

The raw extraction is pinned on the build host. No source external is an axiom
or a selected implementation. The port is a reference model, not a new P6
shipped=reference verdict for the whole forest.
"""
from pathlib import Path
import hashlib, json, re, subprocess, sys
H=Path(__file__).resolve().parent
raw=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-builder-ref9-20261021/drop-opaque-validator/generated/Admission-renamed.lean'],text=True)
assert hashlib.sha256(raw.encode()).hexdigest()=='63c3044dbe71069d760fef6ff9006a8bd887f815b2301bae1e689fe4ece2b754'
s=raw[raw.index('/-- [aspis_core::field::P]'):]
s=s.replace('end AspisBuilderForestDropP6','')
s=re.sub(r'@\[discriminant [^\]]+\]\n','',s)
# Env J uses U32 shift counts. Preserve their literal/type provenance.
s=s.replace('Std.U64.wrapping_shr i level','R1Z.BuilderStdModels.shift64 i level')
s=s.replace('Std.U64.wrapping_shr e 1#i32','Std.U64.wrapping_shr e 1#u32')
s=s.replace('Std.U64.wrapping_shl i i2','Std.U64.wrapping_shl i (UScalar.cast .U32 i2)')
s=s.replace('Std.U64.wrapping_shr p.next_pair_index n','R1Z.BuilderStdModels.shift64 p.next_pair_index n')
s=s.replace('Std.U64.wrapping_shr leaf_index carry_level','R1Z.BuilderStdModels.shift64 leaf_index carry_level')
s=s.replace('Std.U32.wrapping_shr c tupled_args','Std.U32.wrapping_shr c (UScalar.cast .U32 tupled_args)')
s=s.replace('Std.U32.wrapping_shr pvpinwv.membership.index i','Std.U32.wrapping_shr pvpinwv.membership.index (UScalar.cast .U32 i)')
# The three excluded source declarations stay explicit parameters, using
# instance binders so each generated dependent carries precisely its needs.
externals={
'poseidon2.external_linear_lazy':'ExternalLinear',
'pool_v1.pair_forest_copy_builder.records':'Records',
'state_only_trace.StateOnlyTraceFoundation.Insts.CoreOpsDropDrop.drop':'Drop',
}
for name,cl in externals.items():
 pat=r'axiom '+re.escape(name)+r'\s*:\s*([\s\S]*?)(?=\n/--)'
 m=re.search(pat,s); assert m,name
 ty=m.group(1).strip()
 rep=f'class {cl} where\n  call : {ty}\n\nvariable [source{cl} : {cl}]\n\ndef {name} := source{cl}.call\n'
 s=s[:m.start()]+rep+s[m.end():]
# Keep the generated borrow-back functions verbatim; add a proved ABI adapter
# rather than pretending their first projection is a Unit return value.
for suffix in ['closure_1','closure']:
 base=f'poseidon2.hash_fields_with_trace.{suffix}.Insts.CoreOpsFunction'
 mut=base+'FnMutTuplePoseidon2RoundTransitionTuple.call_mut'
 once=base+'FnOnceTuplePoseidon2RoundTransitionTuple.call_once'
 def block(name):
  m=re.search(r'^def\s+'+re.escape(name)+r'(?=\s)',s,re.M);assert m,name
  end=s.find('/--',m.end());return m.start(),end,s[m.start():end]
 a,b,d=block(mut)
 rawmut=d.replace(mut,mut+'_borrow',1)
 # Grab the exact generic binder and state/arg types from the generated body.
 signature=d[d.index('  {F : Type}'):d.index('  Result')]
 signature=signature[:signature.rfind(':')+1]
 wrapper=f'def {mut}\n'+signature+f'\n  Result (Unit × poseidon2.hash_fields_with_trace.{suffix} F) :=\n  R1Z.BuilderForestCallbackAdapter.borrowToPair\n    ({mut}_borrow\n      coreopsfunctionFnMutFPairUsizePoseidon2RoundTransitionTupleInst) c tupled_args\n\n'
 s=s[:a]+rawmut+wrapper+s[b:]
 a,b,d=block(once)
 rawonce=d.replace(once,once+'_state',1).replace(mut+'\n',mut+'_borrow\n')
 signature=d[d.index('  {F : Type}'):d.index('  Result')]
 signature=signature[:signature.rfind(':')+1]
 wrapper=f'def {once}\n'+signature+f'\n  Result Unit := do\n  let _ ← {once}_state\n    coreopsfunctionFnMutFPairUsizePoseidon2RoundTransitionTupleInst c prt\n  ok ()\n\n'
 s=s[:a]+rawonce+wrapper+s[b:]
# Generated unit-valued closures return only state. Use the total state/pair
# isomorphism and preserve their original definitions under a suffix.
for base,argtype,argname in [
 ('poseidon2.hash_fields.closure','(Std.Usize × poseidon2.Poseidon2RoundTransition)','tupled_args'),
 ('poseidon2.merkle_node_compress_v3.closure','poseidon2.Poseidon2RoundTransition','tupled_args')]:
 pattern=r'(def\s+)('+re.escape(base)+r'\.Insts\.CoreOpsFunctionFnMut\S+\.call_mut)([\s\S]*?)(?=\n/--)'
 m=re.search(pattern,s);assert m,base
 name=m.group(2); d=m.group(0).replace(name,name+'_state',1)
 wrapper=f'\n\ndef {name} (c : {base}) ({argname} : {argtype}) :\n  Result (Unit × {base}) :=\n  R1Z.BuilderForestCallbackAdapter.stateToPair {name}_state c {argname}\n'
 s=s[:m.start()]+d+wrapper+s[m.end():]
# The shared-borrow specialization of permute needs the updated callback.
# Thread it through the final loop; keep the original owned API by discarding
# that environment only in its wrapper, after all rounds have executed.
for name in ['poseidon2.permute_optimized_with_trace_loop2','poseidon2.permute_optimized_with_trace']:
 m=re.search(r'^def '+re.escape(name)+r'\s',s,re.M);assert m
 end=s.find('/--',m.end());d=s[m.start():end]
 d=d.replace('Result (Array aspis_core.field.M31 16#usize)','Result ((Array aspis_core.field.M31 16#usize) × F)',1)
 if name.endswith('loop2'): d=d.replace('| none => ok state','| none => ok (state, trace)')
 else:
  d=d.replace('def '+name,'def '+name+'_threaded',1)
  wrapper='''def poseidon2.permute_optimized_with_trace
  {F : Type} (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
  (state : Array aspis_core.field.M31 16#usize) (trace : F) :
  Result (Array aspis_core.field.M31 16#usize) := do
  let (next, _) ← poseidon2.permute_optimized_with_trace_threaded callback state trace
  ok next

'''
  d+=wrapper
 s=s[:m.start()]+d+s[end:]
# Only these two call sites borrow the trace environment across permute.
a=s.index('def poseidon2.hash_fields_with_trace_loop0\n')
b=s.index('/-- [aspis_statement::poseidon2::hash_fields::closure]',a)
s=s[:a]+s[a:b].replace('poseidon2.permute_optimized_with_trace\n','poseidon2.permute_optimized_with_trace_threaded\n')+s[b:]
s=s.replace('(spend.nullifier_reference.hash_owned)','(fun p => spend.nullifier_reference.hash_owned p.1 p.2)')
prefix='''-- Reference-model ABI port; generated by builder-cont11-port.py.
import R1Z.BuilderForestCallbackAdapter
import R1Z.BuilderStdShift
import Aeneas.Tactic.RustAttributes
open Aeneas Aeneas.Std Result ControlFlow Error
open R1Z.BuilderForestStdPort
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section
namespace R1Z.BuilderForestAdmissionPort
'''
audit=['poseidon2.permute_optimized_with_trace_threaded','poseidon2.hash_fields_with_trace','spend.nullifier_reference.derive_nullifier_owned','pool_v1.incremental_merkle.tree_reference.validate_owned','pool_v1.pair_forest_copy_builder.parts','pool_v1.pair_forest_trace.compile_forest_from_copies']
s=prefix+s+'\n'+''.join('#print axioms '+n+'\n' for n in audit)+'end R1Z.BuilderForestAdmissionPort\n'
assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',re.sub(r'--[^\n]*','',s))
p=H.parent/'lean/R1Z/BuilderForestAdmissionPort.lean'
if '--check' in sys.argv: assert p.read_text()==s
else: p.write_text(s)
receipt=dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),port_sha256=hashlib.sha256(s.encode()).hexdigest(),source_externals=externals,callbacks='generated borrow functions retained; borrowToPair/stateToPair; threaded final permutation loop',status='ABI reference model with explicit source-function instance parameters; no whole-source equality claimed',audits=audit)
if '--check' in sys.argv: assert json.loads((H/'builder-cont11-port.json').read_text())==receipt
else: (H/'builder-cont11-port.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(p,hashlib.sha256(s.encode()).hexdigest())
