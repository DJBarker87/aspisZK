#!/usr/bin/env python3
"""Render bounded per-round Lean cells from optimized Rust numeric output."""
from pathlib import Path
import argparse,json,hashlib
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parents[2]
evidence=root/'evidence/pv-runjoin-20261026'
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
records={}
for line in (evidence/'sentinel-states.txt').read_text().splitlines():
 a,b,rest=line.split(' ',2);state=json.loads(rest)
 assert len(state)==16 and all(isinstance(x,int) and 0<=x<2147483647 for x in state)
 records[int(a),int(b)]=state
assert len(records)==72
header='set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_Sentinel\nopen R0P\nabbrev Scalar := PV_RunJoin_FixtureRecords.M\n'
def vector(xs): return '!['+','.join(map(str,xs))+']'
def index(j,n):
 if j==0:return "0"
 return "("+"Fin.succ ("*j+f"(0 : Fin {n-j})"+")"*j+")"
def cell(a,b):
 out=f'def s_{a}_{b} : Fin 16 → Scalar := {vector(records[a,b])}\n'
 if b==0:return out
 if b==1:expr=f'poseidonExternalLinear s_{a}_0'
 elif 2<=b<=5:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalInitial {index(b-2,4)})'
 elif 6<=b<=19:expr=f'poseidonInternalRound s_{a}_{b-1} (poseidonInternalConstants {index(b-6,14)})'
 else:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalFinal {index(b-20,4)})'
 out+=f'theorem round_{a}_{b} : {expr} = s_{a}_{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms round_{a}_{b}\n'
 return out
files={}
files['PV_RunJoin_SentinelPreflight.lean']='import R1Z.PV_RunJoin_FixtureRecords\n'+header+''.join(cell(0,b) for b in range(3))+'end R1Z.PV_RunJoin_Sentinel\n'
for a in range(3):
 prev='SentinelPreflight' if a==0 else f'SentinelPermutation{a-1}'
 text=f'import R1Z.PV_RunJoin_{prev}\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_Sentinel\nopen R0P\n'
 text+=''.join(cell(a,b) for b in range(3 if a==0 else 0,24))
 text+=f'theorem permutation_{a} : poseidonPermutation s_{a}_0 = s_{a}_23 := by\n'
 text+='  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]\n'
 text+='  rw ['+','.join(f'round_{a}_{b}' for b in range(1,24))+']\n'
 text+=f'#print axioms permutation_{a}\nend R1Z.PV_RunJoin_Sentinel\n'
 files[f'PV_RunJoin_SentinelPermutation{a}.lean']=text
for name,text in files.items():
 target=lean/name
 if args.check:assert target.read_text()==text,target
 else:target.write_text(text)
print(json.dumps({'check':args.check,'files':list(files),'cells':69,'max_recurrence_depth_per_cell':1,'numeric_sentinel':records[2,23][7],'sha256':{n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()}},indent=2))
