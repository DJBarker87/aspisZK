from pathlib import Path
import re,json,hashlib,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
source=R/'docs/research/100bit-spend-path-20261013/lean-candidates/query-geometry-source-values-20261020/sources/GeneratedFuns-v1.lean'
s=source.read_text(); tables={}
for k in ['A','B']:
 a=s.index('def fast_domain.TABLE_'+k);b=s.index('\n/--',a)
 tables[k]=[tuple(map(int,m)) for m in re.findall(r'\((\d+)#u32,\s*(\d+)#u32\)',s[a:b])]
 assert len(tables[k])==512
queries=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813]
records=[];outputs={};pmod=2147483647
for row,q in enumerate(queries):
 lines=['import JFs_TX2_TableRead','set_option autoImplicit false','noncomputable section',f'namespace AspisR1.JGp_Geo{row}','open Aeneas Aeneas.Std Result','open AspisR1QueryGeometryActual']
 vals=[q,(q//4)*4,(q//4)*4+3];seen={}
 for kind,u in enumerate(vals):
  lo=u%512;hi=u//512;a,b=tables['A'][lo],tables['B'][hi]
  x=(a[0]*b[0]-a[1]*b[1])%pmod;y=(a[0]*b[1]+a[1]*b[0])%pmod
  lines += [f'def value{kind} : domain.Point U32 := ⟨{x}#u32,{y}#u32⟩']
  if u in seen:
   old=seen[u];lines += [f'theorem source{kind} : fast_domain.fibre_point R17CurrentCM31Semantics.operations {u}#usize=ok value{kind} := source{old}']
  else:
   lines += [f'theorem source{kind} : fast_domain.fibre_point R17CurrentCM31Semantics.operations {u}#usize=ok value{kind} := by',
    f'  have ra : Array.index_usize fast_domain.TABLE_A {lo}#usize=ok ({a[0]}#u32,{a[1]}#u32) := by',
    '    apply JFs_TX2_TableRead.source','    unfold fast_domain.TABLE_A',f'    change fast_domain.TABLE_A_entries[{lo}]?=some _','    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,'+','.join(f'fast_domain.TABLE_A_chunk_{j:02}_length' for j in range(16))+']','    all_goals rfl',
    f'  have rb : Array.index_usize fast_domain.TABLE_B {hi}#usize=ok ({b[0]}#u32,{b[1]}#u32) := by',
    '    apply JFs_TX2_TableRead.source','    unfold fast_domain.TABLE_B',f'    change fast_domain.TABLE_B_entries[{hi}]?=some _','    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,'+','.join(f'fast_domain.TABLE_B_chunk_{j:02}_length' for j in range(16))+']','    all_goals rfl',
    f'  have mask : {u}#usize &&& 511#usize={lo}#usize := by',
    '    apply UScalar.eq_of_val_eq','    rw [UScalar.val_and]','    all_goals rfl',
    f'  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source {u}#usize {lo}#usize {hi}#usize',
    f'    ({a[0]}#u32,{a[1]}#u32) ({b[0]}#u32,{b[1]}#u32) mask',
    f'    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)',
    f'  change point.x.val=ExtractedCurrentCM31Mul.realWord {a[0]} {a[1]} {b[0]} {b[1]} at vx',
    f'  change point.y.val=ExtractedCurrentCM31Mul.imagWord {a[0]} {a[1]} {b[0]} {b[1]} at vy',
    '  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy',
    f'  have ex : point.x={x}#u32 := UScalar.eq_of_val_eq vx',
    f'  have ey : point.y={y}#u32 := UScalar.eq_of_val_eq vy',
    f'  have same : point=value{kind} := by',
    '    cases point',
    '    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey',
    '  exact same ▸ run']
   seen[u]=kind
  lines += [f'#print axioms source{kind}','']
  records.append(dict(row=row,kind=kind,index=u,lo=lo,hi=hi,a=a,b=b,x=x,y=y))
 lines += [f'end AspisR1.JGp_Geo{row}','end']
 outputs[R/f'lean/JGp_Geo{row}.lean']='\n'.join(lines)+'\n'
outputs[P/'JGp_POINT_VALUES.json']=json.dumps(dict(table_source=str(source.relative_to(R)),table_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),records=records),indent=2)+'\n'
check='--check' in sys.argv
for p,s in outputs.items():
 if check: assert p.read_text()==s,p
 else:p.write_text(s)
print('checked' if check else 'generated',len(records),'point inputs from retained source tables')
