from pathlib import Path
import json
E=Path(__file__).resolve().parent;P=2147483647
state=5
def rng():
 global state
 state=(state*6364136223846793005+1442695040888963407)%(1<<64)
 return (state>>32)%P
rows=[]
for i in range(12):
 power=[0]*4 if i==0 else [P-1]*4 if i==1 else [rng() for _ in range(4)]
 basis=0 if i==0 else P-1 if i==1 else rng()
 raw=[(1<<31)+j for j in range(4)] if i==0 else [(1<<34)-1+(i%4)*(P-1)**2+j for j in range(4)]
 # Last raw cells can exceed the nominal phase bound by <=3, but the exact
 # arithmetic guard still holds. Cross-language testing does not claim domains.
 for flush in [False,True]:rows.append(dict(raw=raw,power=power,basis=basis,flush=flush))
dots=[]
for i in range(6):
 gen=(lambda:0) if i==0 else (lambda:1) if i==1 else (lambda:P-1) if i==2 else rng
 words=[gen() for _ in range(152)];q=[b for w in words for b in w.to_bytes(4,'little')];g=[[gen() for _ in range(8)] for _ in range(29)]
 dots.append(dict(q=q,g=g))
(E/'NEG_FIXTURES.json').write_text(json.dumps(dict(rows=rows,dots=dots),indent=2)+'\n')
def arr(xs,t):return '[ '+', '.join(str(x)+'#'+t for x in xs)+' ]'
def wide(w):
 a,b,c,d,e,f,g,h=[str(x)+'#u32' for x in w]
 return '⟨⟨⟨'+a+','+b+'⟩,⟨'+c+','+d+'⟩⟩,⟨⟨'+e+','+f+'⟩,⟨'+g+','+h+'⟩⟩⟩'
s='import NEG_RowIsolated.Funs\nimport NEG_DotsTypes.Funs\nopen Aeneas Aeneas.Std Result\nnamespace NEG_CrossLanguage\n'
s+='def rows : Result (List (List Nat)) := do\n'
for i,r in enumerate(rows):
 a,b,c,d=[str(x)+'#u32' for x in r['power']]
 s+=f"  let r{i} ← NEG_RowIsolated.update_residue_row (Array.make 4#usize {arr(r['raw'],'u64')}) ⟨⟨{a},{b}⟩,⟨{c},{d}⟩⟩ {r['basis']}#u32 {str(r['flush']).lower()}\n"
s+='  ok [ '+', '.join(f'r{i}.val.map (fun x=>x.val)' for i in range(len(rows)))+' ]\n#eval rows\n'
s+='def byte (n : Nat) : U8 := UScalar.ofNat (n%256) (by have h := Nat.mod_lt n (by decide : 0<256); scalar_tac)\n'
for i,d in enumerate(dots):
 words=[int.from_bytes(bytes(d['q'][j:j+4]),'little') for j in range(0,608,4)]
 s+=f"def words{i} : List Nat := [ "+', '.join(map(str,words))+' ]\n'
 s+=f"def q{i} : Array U8 608#usize := ⟨List.ofFn (fun i : Fin 608 => byte (words{i}.getD (i.val/4) 0 / 256^(i.val%4))), by exact List.length_ofFn⟩\n"
 s+=f"def g{i} : Array NEG_DotsTypes.aspis_core.field.wide_exact.WideExact 29#usize := Array.make 29#usize [ "+', '.join(wide(w) for w in d['g'])+' ]\n'
s+='def dots : Result (List (List Nat)) := do\n'
for i,d in enumerate(dots):
 for j in range(4):
  s+=f'  let d{i}_{j} ← NEG_DotsTypes.fast_dots.four_dots_one q{i} g{i} {j}#usize\n'
  s+=f'  let l{i}_{j} ← NEG_DotsTypes.aspis_core.field.wide_exact.WideExact.to_limbs d{i}_{j}\n'
s+='  ok [ '+', '.join(f'l{i}_{j}.val.map (fun x=>x.val)' for i in range(len(dots)) for j in range(4))+' ]\n#eval dots\nend NEG_CrossLanguage\n'
(E/'NEG_CrossLanguage.lean').write_text(s)
