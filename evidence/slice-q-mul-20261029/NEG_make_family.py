from pathlib import Path
import json
E=Path(__file__).resolve().parent;P=2147483647;state=7
def rng():
 global state
 state=(state*6364136223846793005+1442695040888963407)%(1<<64);return(state>>32)%P
prefixes=[[rng() for _ in range(n)] for n in [0,1,4,5,22,109,110]]
push=[]
for i in range(6):push.append(dict(raw=[[2147483648+j+k*4 for j in range(4)] for k in range(3)],power=[0]*4 if i==0 else [rng() for _ in range(4)],basis=0 if i==0 else rng(),terms=[3,0,1,2,3,7][i],index=i%3))
folds=[]
for i in range(6):
 gen=(lambda:0) if i==0 else(lambda:1) if i==1 else(lambda:P-1) if i==2 else rng
 folds.append(dict(alpha=[gen() for _ in range(8)],a=[[gen() for _ in range(8)] for _ in range(4)],inverse=[gen() for _ in range(5)]))
(E/'NEG_FAMILY_FIXTURES.json').write_text(json.dumps(dict(prefixes=prefixes,push=push,folds=folds),indent=2)+'\n')
arr=lambda a,t:'[ '+', '.join(str(x)+'#'+t for x in a)+' ]'
def wide(w):
 a,b,c,d,e,f,g,h=[str(x)+'#u32' for x in w];return f'⟨⟨⟨{a},{b}⟩,⟨{c},{d}⟩⟩,⟨⟨{e},{f}⟩,⟨{g},{h}⟩⟩⟩'
s='import NEG_PrefixFull.Funs\nimport NEG_FoldsTypes.Funs\nimport NEG_PushActual.Funs\nopen Aeneas Aeneas.Std Result\nnamespace NEG_FamilyEval\n'
s+='def prefixes : Result (List (List Nat)) := do\n'
for i,a in enumerate(prefixes):
 s+=f'  let p{i} ← NEG_PrefixFull.batch_prefix_products ⟨{arr(a,"u32")},by scalar_tac⟩\n'
s+='  ok [ '+', '.join(f'p{i}.1.val.map (fun x=>x.val) ++ [p{i}.2.val]' for i in range(len(prefixes)))+' ]\n#eval prefixes\n'
s+='def pushes : Result (List (List Nat)) := do\n'
for i,d in enumerate(push):
 a,b,c,d0=[str(x)+'#u32' for x in d['power']];raw='[ '+', '.join('Array.make 4#usize '+arr(r,'u64') for r in d['raw'])+' ]'
 s+=f"  let p{i} ← NEG_PushActual.BatchedWeights.push ⟨⟨{raw},by scalar_tac⟩,{d['terms']}#usize⟩ {d['index']}#usize ⟨⟨{a},{b}⟩,⟨{c},{d0}⟩⟩ {d['basis']}#u32\n"
s+='  ok [ '+', '.join(f'(p{i}.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p{i}.terms.val]' for i in range(len(push)))+' ]\n#eval pushes\n'
s+='def words (x : NEG_FoldsTypes.aspis_core.field.wide_exact.WideExact) : List Nat :=\n [x.c0.c0.a.val,x.c0.c0.b.val,x.c0.c1.a.val,x.c0.c1.b.val,x.c1.c0.a.val,x.c1.c0.b.val,x.c1.c1.a.val,x.c1.c1.b.val]\n'
s+='def folds : Result (List (List Nat)) := do\n'
for i,d in enumerate(folds):
 a='Array.make 4#usize [ '+', '.join(wide(w) for w in d['a'])+' ]';inv='Array.make 5#usize '+arr(d['inverse'],'u32')
 s+=f'  let c{i} ← NEG_FoldsTypes.circle_fold_with_inverses {wide(d["alpha"])} ({a}) ({inv})\n'
 s+=f'  let l{i} ← NEG_FoldsTypes.line_fold_with_inverses {wide(d["alpha"])} ({a}) ({inv})\n'
s+='  ok [ '+', '.join(f'words c{i} ++ words l{i}' for i in range(len(folds)))+' ]\n#eval folds\nend NEG_FamilyEval\n'
(E/'NEG_FamilyEval.lean').write_text(s)
