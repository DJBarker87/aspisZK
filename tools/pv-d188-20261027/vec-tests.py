# Build only small testing modules; all copied loop bodies remain byte-identical.
exec(__import__('pathlib').Path('tools/pv-d188-20261027/more-tests.py').read_text())
from pathlib import Path
base=preamble
preamble=preamble.replace('import R1Z.ProverRwFullTypes','import R1Z.ProverRwFullTypes\nimport R1Z.PV_CB_Op105Funs\nimport R1Z.PV_CB_Op109Funs')
extra='''
abbrev aspis_core.r0.domain.Point := ProverRwFull.aspis_core.r0.domain.Point
abbrev aspis_core.field.M31.Insts.CoreCloneClone := core.clone.CloneU32
private def vec {T : Type} (s : Slice T) : alloc.vec.Vec T := ⟨s.val,s.property⟩
'''
preamble+=extra
preamble=preamble.replace("open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull", "open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull R1Z")
m=Path('evidence/pv-d188-20261027/tests/PV_D188_OwnedCellsEval.lean').read_text();m=m[m.index('private def mfield'):m.index('#eval')];preamble+=m+'\n'
emit('PV_D188_SplitVecEval',['host_commitment.split_coefficients_loop'],'''#eval (do
 let s ← lift (Array.to_slice (Array.make 4#usize [1#u32,2#u32,3#u32,4#u32]))
 let z ← lift (Array.to_slice (Array.repeat 2#usize 0#u32))
 let (a,b) ← host_commitment.split_coefficients_loop s (vec z) (vec z) 0#usize
 ok (a.val.map (fun x => x.val),b.val.map (fun x => x.val)) : Result (List Nat × List Nat))''')
emit('PV_D188_MergeVecEval',['host_commitment.merge_evaluations_loop'],'''#eval (do
 let nodes ← lift (Array.to_slice (Array.make 2#usize [1#u32,2#u32]))
 let a ← lift (Array.to_slice (Array.make 1#usize [3#u32]))
 let b ← lift (Array.to_slice (Array.make 1#usize [4#u32]))
 let z ← lift (Array.to_slice (Array.repeat 2#usize 0#u32))
 let v ← host_commitment.merge_evaluations_loop mfield nodes a b (vec z) 0#usize
 ok (v.val.map (fun x => x.val)) : Result (List Nat))''')
emit('PV_D188_DomainNextEval',['host_commitment.domain_next_level_loop'],'''#eval (do
 let a ← lift (Array.to_slice (Array.make 4#usize [2#u32,3#u32,4#u32,5#u32]))
 let z ← lift (Array.to_slice (Array.repeat 2#usize 0#u32))
 let v ← host_commitment.domain_next_level_loop a (vec z) 0#usize
 ok (v.val.map (fun x => x.val)) : Result (List Nat))''')
emit('PV_D188_DomainFirstEval',['host_commitment.domain_first_level_loop'],'''#eval (do
 let a ← lift (Array.to_slice (Array.repeat 1024#usize ({x := 2#u32,y := 0#u32} : aspis_core.r0.domain.Point U32)))
 let z ← lift (Array.to_slice (Array.repeat 1024#usize 0#u32))
 let v ← host_commitment.domain_first_level_loop a 1024#usize (vec z) 0#usize
 ok (v.val.take 4 |>.map (fun x => x.val)) : Result (List Nat))''')
emit('PV_D188_Clone0Eval',['host_semantic.clone_semantic_columns_loop0'],'''#eval (do
 let s ← lift (Array.to_slice (Array.make 1#usize [5#u32]))
 let z ← lift (Array.to_slice (Array.make 1#usize [0#u32]))
 let noised ← lift (Array.to_slice (Array.repeat 16#usize (vec s)))
 let (v,_) ← host_semantic.clone_semantic_columns_loop0 noised (Array.repeat 26#usize (vec z)) 0#usize
 ok (v.val.map (fun a => a.val.map (fun x => x.val))) : Result (List (List Nat)))''')
emit('PV_D188_Clone1Eval',['host_semantic.clone_semantic_columns_loop1'],'''#eval (do
 let s ← lift (Array.to_slice (Array.make 1#usize [7#u32]))
 let z ← lift (Array.to_slice (Array.make 1#usize [0#u32]))
 let v ← host_semantic.clone_semantic_columns_loop1 (Array.repeat 10#usize (vec s)) (Array.repeat 26#usize (vec z)) 16#usize
 ok (v.val.map (fun a => a.val.map (fun x => x.val))) : Result (List (List Nat)))''')
(out/'more-test-binding.json').write_text(json.dumps(manifest,indent=2)+'\n')
