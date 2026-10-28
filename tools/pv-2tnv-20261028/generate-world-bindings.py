from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume'
names=['JHb_DataMaster','JHg_DataMaster','JHb_DataForest','JHg_DataForest','JHb_DataLane','JHb_DataRegistry','JHb_DataEntry','JFx_DataPublic00']
chunks={};data={}
for m in names:
 s=(E/(m+'.lean.txt')).read_text();chunks[m]=re.findall(r'^def (c\d+)',s,re.M);b=[]
 for l in s.splitlines():
  if re.match(r'def c\d+',l):
   if 'replicate' in l:
    n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',l).groups());b.extend([v]*n)
   else:b.extend(map(int,re.findall(r'(\d+)#u8',l)))
 data[m]=bytes(b)
public='JFx_DataPublic00'
facts=[('master_pool','JHg_DataMaster',72,public,8,32),('forest_pool','JHg_DataForest',8,public,8,32),('master_domain','JHg_DataMaster',176,public,256,32),('forest_domain','JHg_DataForest',40,public,256,32),('forest_anchor','JHg_DataForest',80,public,112,32),('lane_pool','JHb_DataLane',40,public,8,32),('lane_snapshot_index','JHb_DataLane',88,public,296,8),('lane_snapshot_root','JHb_DataLane',96,public,304,32),('lane_snapshot_frontier','JHb_DataLane',128,public,336,640),('registry_pool','JHb_DataRegistry',8,public,8,32),('entry_pool','JHb_DataEntry',8,public,8,32)]
rules='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
s='import PV_2TNV_SourceBytes\n'+''.join('import '+m+'\n' for m in names if m!=public)+'''set_option autoImplicit false
namespace AspisR1.PV_2TNV_WorldData
open Aeneas Aeneas.Std
/-- Compare bounded windows symbolically, avoiding reduction of a 640-byte list. -/
theorem chunks {A : Type} (xs ys : List A) (a b n : Nat) :
    (∀ i, i < n → (xs.drop (a+32*i)).take 32 = (ys.drop (b+32*i)).take 32) →
    (xs.drop a).take (32*n) = (ys.drop b).take (32*n) := by
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [Nat.mul_succ,List.take_add]
    apply congrArg₂ List.append
    · exact ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    · simpa only [List.drop_drop] using h n (Nat.lt_succ_self n)
#print axioms chunks
'''
for name,m,a,n,b,count in facts:
 assert data[m][a:a+count]==data[n][b:b+count],name
 s+=f'theorem {name} : ({m}.value.val.drop {a}).take {count} = ({n}.bytes.drop {b}).take {count} := by\n'
 s+=f'  change ({m}.bytes.drop {a}).take {count} = ({n}.bytes.drop {b}).take {count}\n'
 if count==640:
  s+=f'  apply chunks {m}.bytes {n}.bytes {a} {b} 20\n  intro i hi\n  interval_cases i <;>\n    simp only ['+m+'.bytes,'+n+'.bytes,'+','.join(t+'.'+c+'_length' for t in [m,n] for c in chunks[t])+',Nat.reduceMul,'+rules+']\n  all_goals rfl\n#print axioms '+name+'\n'
 else:
  s+='  simp only ['+m+'.bytes,'+n+'.bytes,'+','.join(t+'.'+c+'_length' for t in [m,n] for c in chunks[t])+','+rules+']\n  rfl\n#print axioms '+name+'\n'
s+='end AspisR1.PV_2TNV_WorldData\n'
p=R/'lean/PV_2TNV_WorldData.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
(E/'world-data-generation.json').write_text(json.dumps(dict(facts=facts,source_sha256=hashlib.sha256(s.encode()).hexdigest(),input_sha256={m:hashlib.sha256(v).hexdigest() for m,v in data.items()},classification='literal byte associations; no entry or wrapper execution theorem'),indent=2)+'\n')
print('checked',len(facts),'source data associations')
