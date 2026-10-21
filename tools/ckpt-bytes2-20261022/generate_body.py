from pathlib import Path
root=Path(__file__).resolve().parents[2]
out=root/'docs/research/100bit-spend-path-20261013/lean/CheckpointBytesBody.lean'
s='''import CheckpointBytesLookup
import CheckpointBytesHeader
import CheckpointBytesSparseDigest
import CheckpointBytesSparseE
import CheckpointBytesSparseK
import CheckpointBytesQuery

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytesBody
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted
open aspis_r1_cost_probe.verifier
open CheckpointBytesBlocks CheckpointBytesDigest
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec
open MultiproofConeCanonical OraclePortCompactDraft
attribute [local irreducible] OraclePortCkptAbi2Extracted.body_byte

def fields (p : Prepared) (a : Accumulator) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144) : Fields where
  state := stateOf p.state
  roots := fun j => stateOf (p.roots.val[j.val]'(by simpa [p.roots.property] using j.isLt))
  gamma := p.gamma
  kappa := p.kappa
  alpha := fun j => p.alpha.val[j.val]'(by simpa [p.alpha.property] using j.isLt)
  rho := p.rho
  queries := fun j => ⟨(p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val,qb j⟩
  semanticAlpha := fun j => p.semantic_alpha.val[j.val]'(by simpa [p.semantic_alpha.property] using j.isLt)
  coordinates := fun j => match j.val with
    | 0 => (p.z.val[0]'(by simp [p.z.property])).x
    | 1 => (p.z.val[0]'(by simp [p.z.property])).y
    | 2 => (p.z.val[1]'(by simp [p.z.property])).x
    | _ => (p.z.val[1]'(by simp [p.z.property])).y
  claim := p.claim
  rhs := a.rhs
  power := a.power
  weights := fun j => a.weights.val[j.val]'(by rw [size]; exact j.isLt)

'''
# Small block selection lemmas keep whole-body proof symbolic.
entries=[('header',0,16,None),('proofHash',16,32,None),('publicHash',48,32,None),('state',80,32,None),('root0',112,32,None),('root1',144,32,None),('gamma',176,32,'gamma'),('kappa',208,32,'kappa'),('alpha0',240,32,'alpha'),('alpha1',272,32,'alpha'),('rho',304,16,'rho'),('query',320,88,None),('semantic',408,160,'semanticAlpha'),('coordinate0',568,16,'coordinates'),('coordinate1',584,16,'coordinates'),('coordinate2',600,16,'coordinates'),('coordinate3',616,16,'coordinates'),('claim',632,32,'claim'),('rhs',664,32,'rhs'),('power',696,16,'power'),('weight',712,1024,'weights')]
# 18 block lookup equalities, field RHS is left abstract using blocks index.
s+='''theorem body_block (p : OraclePortCheckpointAbiC5.Prepared)
    (a : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (hp hu : AspisV8R19.SourceDuplexStep.State) (j : Fin 18) (i : Nat)
    (bound : i < (OraclePortCheckpointAbiC5.widths[j.val]'(by have := j.isLt; simp [OraclePortCheckpointAbiC5.widths] <;> omega))) :
    (OraclePortCheckpointAbiC5.body p a hp hu)[OraclePortCheckpointAbiC5.offsets[j.val]'(by have := j.isLt; simp [OraclePortCheckpointAbiC5.offsets] <;> omega)+i]? =
      ((OraclePortCheckpointAbiC5.blocks p a hp hu)[j.val]'(by have := j.isLt; simp [OraclePortCheckpointAbiC5.blocks] <;> omega))[i]? := by
  apply CheckpointBytesLookup.body_byte p a hp hu j _ (List.getElem?_eq_getElem _) i
  have widths := congrArg (fun xs : List Nat => xs[j.val]?) (OraclePortCheckpointAbiC5.block_widths p a hp hu)
  simp only [List.getElem?_map] at widths
  have index : j.val < (OraclePortCheckpointAbiC5.blocks p a hp hu).length := by have := j.isLt; simp [OraclePortCheckpointAbiC5.blocks] <;> omega
  rw [List.getElem?_eq_getElem index,Option.map_some,List.getElem?_eq_getElem (show j.val < OraclePortCheckpointAbiC5.widths.length by simpa [OraclePortCheckpointAbiC5.widths] using j.isLt)] at widths
  have eqn := Option.some.inj widths
  rw [← eqn] at bound
  exact bound

'''
s+='''theorem body_byte_c5 (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)
    (i : Usize) (bound : i.val < 1736) :
    ∃ v, OraclePortCkptAbi2Extracted.body_byte p a hp hu i = ok v ∧
      (OraclePortCheckpointAbiC5.body (prepared (fields p a size qb) canonical)
        (accumulator (fields p a size qb) canonical) (stateOf hp) (stateOf hu))[i.val]? =
          some (AspisV8R19.SqueezeOracleBridge.decodeByte v) := by
'''
# introduce index cases preserving numeric bounds; use helper for block mapping.
for n,(name,start,width,canon) in enumerate(entries):
 end=start+width
 # coord widths each separate
 if n!=len(entries)-1:s+=f'  by_cases h{end} : i.val < {end}\n  · '
 else:s+='  '
 indent='    ' if n!=len(entries)-1 else '  '
 # preceding failures in context enable omega
 if name=='header':
  s+='have localByte := CheckpointBytesHeader.header_bytes p a hp hu next ⟨i.val,h16⟩\n'
  off='i.val';jblock=0
 else:
  vector=name in ['query','semantic','weight']
  w=4 if name=='query' else 16 if vector else width
  off=f'(i.val-{start})'
  args=''
  if vector:
   count={'query':22,'semantic':10,'weight':64}[name]
   s+=f'have ordinal : (i.val-{start})/{w} < {count} := by omega\n'
   s+=indent+f'let j : Fin {count} := ⟨(i.val-{start})/{w},ordinal⟩\n'
   s+=indent+f'let k := Usize.ofNat ((i.val-{start})%{w}) (by scalar_tac)\n'
   s+=indent+f'have kb : k.val < {w} := by simp [k]; omega\n'
   args=' size j' if name=='weight' else ' j'
   off=f'{w}*j.val+k.val'
  else:
   s+=f'let k := Usize.ofNat (i.val-{start}) (by scalar_tac)\n'
   s+=indent+f'have kb : k.val < {width} := by simp [k]; omega\n'
   off='k.val'
  ns='CheckpointBytesSparseDigest' if name in ['proofHash','publicHash','state','root0','root1'] else 'CheckpointBytesQuery' if name=='query' else 'CheckpointBytesSparseE' if width==32 else 'CheckpointBytesSparseK'
  suffix='bytes' if ns in ['CheckpointBytesSparseDigest','CheckpointBytesQuery'] else 'c5'
  carg=''
  if canon:
   carg={'alpha0':' (canonical.alpha 0)','alpha1':' (canonical.alpha 1)', 'semantic':' (canonical.semanticAlpha j)','weight':' (canonical.weights j)'}.get(name, f' (canonical.coordinates {int(name[-1])})' if name.startswith('coordinate') else f' canonical.{canon}')
  s+=indent+f'have localByte := {ns}.{name}_{suffix} p a hp hu{args}{carg} k kb\n'
  s+=indent+f'have idx : {start}+{off} = i.val := by '+('simp [j,k]; omega' if vector else 'simp [k]; omega')+'\n'
  s+=indent+'simp only [idx] at localByte\n'
  s+=indent+'have cast : Usize.ofNat i.val (by scalar_tac) = i := by apply UScalar.eq_of_val_eq; rfl\n'
  s+=indent+'rw [cast] at localByte\n'
  jblock= n if n<14 else n-3 if n>=17 else 13 # fix explicitly below
  jblock={'coordinate0':13,'coordinate1':13,'coordinate2':13,'coordinate3':13,'claim':14,'rhs':15,'power':16,'weight':17}.get(name,n)
 # lookup position is full block for coords use 16*c+k
 blockoff=f'16*{int(name[-1])}+k.val' if name.startswith('coordinate') else off
 s+=indent+f'have lookup := body_block (prepared (fields p a size qb) canonical) (accumulator (fields p a size qb) canonical) (stateOf hp) (stateOf hu) ⟨{jblock},by decide⟩ ({blockoff}) (by '+ ('simp [OraclePortCheckpointAbiC5.widths]; omega' if name=='header' else 'simp [OraclePortCheckpointAbiC5.widths]; '+('have := j.isLt; omega' if name in ['query','semantic','weight'] else 'omega'))+')\n'
 s+=indent+'simp only [OraclePortCheckpointAbiC5.offsets,OraclePortCheckpointAbiC5.blocks,List.getElem_cons_zero,List.getElem_cons_succ,prepared,accumulator,fields] at lookup\n'
 if name!='header':
  if name.startswith('coordinate') or name in ['semantic','query','weight']:
   # vector bytes expansion
   vwidth=4 if name=='query' else 16
   vec='OraclePortCheckpointAbiC5.queryBytes' if name=='query' else 'OraclePortCheckpointAbiC5.encodeKs'
   s+=indent+f'unfold {vec} at lookup\n'
   if name!='query':s+=indent+'unfold FixedWidthDecoder.encode at lookup\n'
   s+=indent+'rw [List.flatMap_def,List.map_ofFn] at lookup\n'
   ordinalarg=f'⟨{int(name[-1])},by decide⟩' if name.startswith('coordinate') else 'j'
   lenproof='by intro j; exact OraclePortCheckpointAbiC5.encodeK_length _' if name!='query' else 'by intro j; simp [le32]'
   s+=indent+f'rw [CheckpointBytesLookup.vector_byte _ {vwidth} ({lenproof}) ({ordinalarg}) k.val kb] at lookup\n'
  s+=indent+f'have pos : '+('568+(16*'+name[-1]+'+k.val)' if name.startswith('coordinate') else f'{start}+({off})')+' = i.val := by '+('simp [j,k]; omega' if name in ['query','semantic','weight'] else 'simp [k]; omega')+'\n'
  s+=indent+'rw [pos] at lookup\n'
 else:
  s+=indent+'simp only [Nat.zero_add] at lookup\n'
 s+=indent+'obtain ⟨v,run,byte⟩ := localByte\n'+indent+'refine ⟨v,run,?_⟩\n'+indent+'exact lookup.trans byte\n'
s+='\n#print axioms body_block\n#print axioms body_byte_c5\nend AspisR1.CheckpointBytesBody\nend\n'
import sys
if '--check' in sys.argv:
 assert out.read_text()==s
else:out.write_text(s)
