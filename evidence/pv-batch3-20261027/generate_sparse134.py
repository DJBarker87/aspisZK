"""Emit named sparse endpoint states and eight-step certificates, never run reduction.
Only each queried U8 count / 136-entry constant table cell is reduced. The
1024-cell arrays are handled by SparseArray/SparseSet symbolic theorems.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path(__file__).resolve().parent; L=D/'lean'
def emit(path,text):
 if '--check' in sys.argv: assert path.read_text()==text, str(path)
 else: path.write_text(text)
raw=(L/'PV_B3_Forest_134_Funs.lean').read_text()
table=raw.split('Array.make 136#usize [',1)[1].split(']',1)[0]
links=[tuple(map(int,m)) for m in re.findall(r'\((\d+)#u16,\s*(\d+)#u16\)',table)]
assert len(links)==136
P={};C={};counts=[]
for a,b in links:
 assert 0<=a<1024 and 0<=b<1024
 counts.append((P.get(a,0),C.get(b,0)))
 assert max(counts[-1])<2
 P[a]=P.get(a,0)+1;C[b]=C.get(b,0)+1
s='''import PV_B3_MaskSparseStep
namespace PV_B3_MaskSparseStates
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep
set_option autoImplicit false
abbrev State := Array U8 1024#usize × Array U8 1024#usize × Array U16 64#usize × Usize
abbrev Final := core.result.Result (Array U16 64#usize)
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
def body (s : State) : Result (ControlFlow State Final) :=
  host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
    s.1 s.2.1 s.2.2.1 s.2.2.2
def run (s : State) : Result Final := loop body s
def P000 : Nat → U8 := fun _ => 0#u8
def C000 : Nat → U8 := fun _ => 0#u8
def M000 : Nat → U16 := fun _ => 0#u16
'''
for i,(a,b) in enumerate(links):
 j=i+1;np,nc=counts[i]
 s+=f'def P{j:03} : Nat → U8 := Function.update P{i:03} {a} {np+1}#u8\n'
 s+=f'def C{j:03} : Nat → U8 := Function.update C{i:03} {b} {nc+1}#u8\n'
 s+=f'def M{j:03} : Nat → U16 := mark (mark M{i:03} {a}#usize) {b}#usize\n'
for i in range(137):
 s+=f'def s{i:03} : State := (array 1024#usize P{i:03}, array 1024#usize C{i:03}, array 64#usize M{i:03}, {i}#usize)\n'
s+='''theorem run_next (s t : State) (h : body s = ok (cont t)) : run s = run t := by
  unfold run
  rw [loop.eq_def, h]
#print axioms body
#print axioms run
#print axioms run_next
'''
for prefix in ['P','C','M','s']:
 for i in range(137):s+=f'#print axioms {prefix}{i:03}\n'
s+='end PV_B3_MaskSparseStates\n'
emit(L/'PV_B3_MaskSparseStates.lean',s)
for chunk in range(17):
 start=8*chunk
 mod=f'PV_B3_MaskSparse{chunk:02}'
 s='import PV_B3_MaskSparseStates\nimport PV_B3_MaskSparseScalar\n'
 if chunk<16:s+=f'import PV_B3_MaskSparse{chunk+1:02}\n'
 s+=f'''namespace {mod}
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
'''
 for i in range(start,start+8):
  a,b=links[i];np,nc=counts[i];j=i+1
  pread='\n'.join('  dsimp only ['+', '.join(f'P{k:03}' for k in range(top,max(-1,top-8),-1))+', Function.update]' for top in range(i,-1,-8))+('\n  all_goals rfl' if i==0 else '\n  rfl')
  cread=pread.replace('P','C')
  s+=f'''theorem link{i:03} : Array.index_usize host_forest.MASK_LINKS {i}#usize = ok ({a}#u16,{b}#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer{i:03} : P{i:03} {a} = {np}#u8 := by
{pread}
theorem consumer{i:03} : C{i:03} {b} = {nc}#u8 := by
{cread}
theorem step{i:03} : body s{i:03} = ok (cont s{j:03}) := by
  unfold body s{i:03} s{j:03} P{j:03} C{j:03} M{j:03}
  have next : Usize.wrapping_add {i}#usize 1#usize = {j}#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value {i}#usize (by
      change {j} < Usize.size; simpa using UScalar.hSize ({j}#usize))
  simpa only [next, show ({a}#usize).val = {a} from rfl,
    show ({b}#usize).val = {b} from rfl] using step P{i:03} C{i:03} M{i:03} {i}#usize {a}#usize {b}#usize {a}#u16 {b}#u16 {np+1}#u8 {nc+1}#u8
    (by decide) link{i:03} (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P{i:03} {a}) = _; rw [producer{i:03}]; rfl) (by change host_forest.mask_endpoint_bump (C{i:03} {b}) = _; rw [consumer{i:03}]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
'''
 # Backward composition uses only checked steps and a previously checked suffix.
 if chunk==16:
  s+='''theorem finish : run s136 = ok (.Ok (array 64#usize M136)) := by
  unfold run
  rw [loop.eq_def]
  change (do let cf ← body s136; match cf with
    | .cont t => loop body t
    | .done value => ok value) = _
  have hd : body s136 = ok (done (.Ok (array 64#usize M136))) := by
    unfold body s136 host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
    rw [if_neg (by decide)]
  rw [hd]
  rfl
'''
  tail='finish'
 else:tail=f'PV_B3_MaskSparse{chunk+1:02}.suffix'
 s+=f'theorem suffix : run s{start:03} = ok (.Ok (array 64#usize M136)) :=\n  '
 for i in range(start,start+8): s+=f'(run_next _ _ step{i:03}).trans ('
 s+=tail+')'*8+'\n'
 for i in range(start,start+8):
  for name in ['link','producer','consumer','step']:s+=f'#print axioms {name}{i:03}\n'
 if chunk==16:s+='#print axioms finish\n'
 s+='#print axioms suffix\n'+f'end {mod}\n'
 emit(L/(mod+'.lean'),s)
metadata=dict(table_sha256=hashlib.sha256(table.encode()).hexdigest(),links=len(links),max_producer_count=max(P.values()),max_consumer_count=max(C.values()),sparse_read_only_kernel_reduction=True,whole_run_kernel_reduction=False,modules=['PV_B3_MaskSparseStates']+[f'PV_B3_MaskSparse{i:02}' for i in range(17)])
emit(D/'sparse134-preflight.json',json.dumps(metadata,indent=2)+'\n')
print(json.dumps(metadata))
