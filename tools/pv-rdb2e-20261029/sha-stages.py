from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(E/'source/sha256-soft.rs').read_text();const=(E/'source/sha-consts.rs').read_text();vals=re.findall(r'0x[0-9a-f]+',const.split('pub const K32:')[1].split('];')[0]);assert len(vals)==64
rows=[]
for i,line in enumerate(re.findall(r'^    (?:schedule_)?rounds4!\(abef, cdgh, .*?\);',s,re.M)):
 nums=[int(n)for n in re.findall(r'\d+',line.split('cdgh,')[1])]
 # Last number is the actual source constant index; preceding wX numbers are banks.
 n=nums[-1];assert n==i
 k=list(reversed(vals[4*i:4*i+4]));kv='⟨'+','.join(k)+'⟩'
 name=f'PV_RDB2E_ShaStage{i:02d}'
 if i<4:
  rest=f'b.w{i}';bank='b';window='';fact=''
 else:
  phase=(i-4)%5;target=[4,0,1,2,3][phase];assert nums[:-1]==[phase,(phase+1)%5,(phase+2)%5,(phase+3)%5,(phase+4)%5],nums
  rest=f'(bank{phase} b).w{target}';bank=f'bank{phase} b'
  window=f'''\ntheorem schedule_at_{i:02d} (b : Banks) :
    window{(phase+1)%5} (stage{i:02d} (join b.w0 b.w1) b).2 = advance (window{phase} b) := phase{phase} b
''';fact=f'#print axioms schedule_at_{i:02d}\n'
 text=f'''import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage {i}; constants and bank operands checked by sha-stages.py. -/
def stage{i:02d} (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ({rest}) ({kv})
  (join pair.1 pair.2,{bank})

theorem rounds_at_{i:02d} (s : S) (b : Banks) :
    (stage{i:02d} s b).1=four s (add ({rest}) ({kv})) :=
  four_source s ({rest}) ({kv})
{window}
#print axioms rounds_at_{i:02d}
{fact}end R1Z.PV_RDB2E_ShaScalar
'''
 (P/(name+'.lean')).write_text(text)
 rows.append(dict(stage=i,source_line=line,constants=k,rest=rest,bank_after=bank,module='R1Z/'+name,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
assert len(rows)==16
(E/'sha-stage-binding.json').write_text(json.dumps(rows,indent=2))
