from pathlib import Path
import re,json,hashlib
out=Path('evidence/pv-d188-20261027');s=Path('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean').read_text();ds=list(re.finditer(r'^def\s+([^\s({:]+)',s,re.M));defs={}
for i,m in enumerate(ds):
 end=ds[i+1].start() if i+1<len(ds) else len(s);doc=s.find('/--',m.start());end=min(end,doc if doc>=0 else end);defs[m[1]]=s[m.start():end].strip()
preamble='''import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace NS
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_prover.state_only_hiding.StateOnlyMaskBuildError := ProverRwFull.aspis_prover.state_only_hiding.StateOnlyMaskBuildError
abbrev aspis_core.field.M31.add := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
abbrev aspis_core.field.M31.sub := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
abbrev aspis_core.field.M31.mul := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
abbrev aspis_core.field.M31.double := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.double
abbrev aspis_core.field.QM31.add := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
abbrev aspis_core.field.QM31.mul := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
abbrev aspis_core.field.QM31.mul_m31 := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
abbrev aspis_core.field.CM31.sub := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
def aspis_core.field.M31.ZERO : Result U32 := ok 0#u32
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 := ok R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
def aspis_core.field.QM31.ONE : Result aspis_core.field.QM31 := ok R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE
def aspis_core.field.QM31.sub (a b : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
 let c0 ← aspis_core.field.CM31.sub a.c0 b.c0
 let c1 ← aspis_core.field.CM31.sub a.c1 b.c1
 ok {c0,c1}
def aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS : Result Usize := ok 1024#usize
def multiproof.LEAF_BITS : Result U32 := ok 18#u32
def multiproof.MAX_BATCH : Result Usize := ok 16#usize
'''
manifest=[]
def emit(name,prefixes,tail):
 names=[n for n in defs if any(n==p or n.startswith(p+'.') or n.startswith(p+'_') for p in prefixes)]
 text=preamble.replace('NS',name)+'\n'+'\n\n'.join(defs[n] for n in names)+'\n'+tail+'\nend '+name+'\n';(out/'tests'/(name+'.lean')).write_text(text);manifest.append(dict(module=name,definitions=[dict(name=n,body_sha256=hashlib.sha256(defs[n].encode()).hexdigest()) for n in names],bindings='Exact field-model primitive definitions and native literal constants supplied to isolate the body. No arbitrary ExternalFuns instance.'))
emit('PV_D188_NodeEval',['host_tree.check_indices','host_tree.count_parent','host_tree.count_level','host_tree.count_levels','host_tree.node_count'],'''#eval (do let s ← lift (Array.to_slice (Array.make 3#usize [1#u32,2#u32,3#u32]))
          let n ← host_tree.node_count s
          ok (n.map (fun x => x.val)) : Result (Option Nat))''')
emit('PV_D188_BooleanEval',['host_semantic.boolean_point'],'''#eval (do let a ← host_semantic.boolean_point 37#usize
          ok (a.val.map (fun q => q.c0.a.val)) : Result (List Nat))''')
emit('PV_D188_AccumulateEval',['host_sumcheck.interpolation_accumulate'],'''#eval (do let one ← aspis_core.field.QM31.ONE
          let scale := {one with c0 := {one.c0 with a:=3#u32}}
          let a ← host_sumcheck.interpolation_accumulate (Array.repeat 28#usize one) (Array.repeat 28#usize 2#u32) scale
          ok (a.val.map (fun q => q.c0.a.val)) : Result (List Nat))''')
emit('PV_D188_BasisCellEval',['host_sumcheck.interpolation_shift','host_sumcheck.interpolation_basis_cell'],'''#eval (do let a ← host_sumcheck.interpolation_basis_cell (Array.repeat 28#usize 2#u32) 1#usize 3#usize
          ok (a.val.map (fun q => q.val)) : Result (List Nat))''')
emit('PV_D188_ExtendEval',['host_sumcheck.interpolation_shift','host_sumcheck.interpolation_basis_cell','host_sumcheck.interpolation_extend'],'''#eval (do let a ← host_sumcheck.interpolation_extend (Array.repeat 28#usize 2#u32) 1#usize 3#usize
          ok (a.val.map (fun q => q.val)) : Result (List Nat))''')
emit('PV_D188_BasisEval',['host_sumcheck.interpolation_shift','host_sumcheck.interpolation_basis_cell','host_sumcheck.interpolation_extend','host_sumcheck.interpolation_basis'],'''#eval (do let (a,d) ← host_sumcheck.interpolation_basis 1#usize
          ok (a.val.map (fun q => q.val),d.val) : Result (List Nat × Nat))''')
emit('PV_D188_AssignmentEval',['host_sumcheck.evaluate_assignment_loop'],'''#eval (do let zero ← aspis_core.field.QM31.ZERO
          let a ← host_sumcheck.evaluate_assignment_loop 1#usize 3#usize 5#usize (Array.repeat 10#usize zero) 0#usize
          ok (a.val.map (fun q => q.c0.a.val)) : Result (List Nat))''')
# Pure balancing helpers become closed after supplying their actual arithmetic/row-count leaves.
for suffix,field in [('M31','M31'),('QM31','QM31')]:
 stem=field.lower();prefix='aspis_prover.state_only_hiding.'
 emit('PV_D188_Balance'+suffix+'Eval',[prefix+'inactive_'+stem+'_step',prefix+'sum_'+stem+'_copy_inactive',prefix+'balance_'+stem+'_copy_inactive'],('''#eval (do
 let z ← aspis_core.field.%s.ONE
 let s ← lift (Array.to_slice (Array.repeat 1024#usize z))
 let (r,s) ← aspis_prover.state_only_hiding.balance_%s_copy_inactive s 3#usize (Array.repeat 1024#usize false)
 let q ← Slice.index_usize s 3#usize
 ok %s : Result Nat)'''%(field,stem,'q.val' if field=='M31' else 'q.c0.a.val')))
(out/'more-test-binding.json').write_text(json.dumps(manifest,indent=2)+'\n')

# Export fixture helpers for the remaining Vec/array writeback checks.
