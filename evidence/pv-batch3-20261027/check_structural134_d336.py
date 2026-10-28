"""Frozen-source structural argument; not a compiler correctness proof.
Check the schedule-constructor trace against MASK_LINKS and emitted constants.
Token pins make every manually reviewed control step explicit and fail closed.
"""
from pathlib import Path
import re,json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent; R=D.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def body(path,name):
 s=(R/path).read_text();a=s.index('{',s.index('fn '+name+'('));i=a+1;depth=1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def tok(s):return re.findall(r'\w+|[^\w\s]',re.sub(r'//[^\n]*','',s))
forest='crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs'
tree='crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs'
profile='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
copy='crates/aspis-prover/src/host_forest.rs'
checks=[(tree,'build_pool_v1_pair_copy_row_schedule_v1'),(tree,'endpoint_counts'),
 (forest,'build_pool_v1_pair_forest_copy_row_schedule_v1'),(forest,'endpoint_counts'),
 (forest,'pool_v1_pair_forest_copy_active_rows_v1'),(forest,'pool_v1_pair_forest_copy_active_row_masks_v1'),
 (forest,'pool_v1_pair_forest_path_base_row_v1'),(forest,'pool_v1_pair_forest_membership_hash_block_v1'),
 (profile,'pool_v1_pair_path_base_row_v1'),(copy,'mask_endpoint_bump'),
 (copy,'pool_v1_pair_forest_copy_active_row_masks_v1')]
pins={p+':'+n:tok(body(p,n)) for p,n in checks}
pinfile=D/'structural134-reviewed-tokens.json'
if '--record-reviewed' in sys.argv:pinfile.write_text(json.dumps(pins,indent=1)+'\n')
assert pins==json.loads(pinfile.read_text()),'reviewed constructor or error/control path changed'
# Constructor trace of the pinned source, in push order. Private links are
# included for the legacy validation, then filtered exactly as the source does.
legacy=[]
def push(p,c,private=False):legacy.append((p,c,private))
for f,t in [(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)]:push(f*16+11,t*16)
for p,c in [(11,28),(12,412),(44,428),(60,428)]:push(p,c)
for l in range(21):
 a=864+(l//4)*16+1+2*(l%4)
 push((3+l)*16+11,a,True);push(a+1,(4+l)*16+12,True);push(a+1,(4+l)*16,True)
for p,c in [(44,960),(460,962),(508,964),(960,966),(962,966),(964,967),(966,967),
 (64,969),(865,969),(523,970),(475,540),(523,540),(970,528)]:push(p,c)
for l in range(20):push((33+l)*16+11,(34+l)*16+12);push((33+l)*16+11,(34+l)*16)
assert len(legacy)==127
links=[(p+48 if p>=864 else p,c+48 if c>=864 else c) for p,c,private in legacy if not private]
for l in range(24):
 a=912+(l//4)*16+[1,5,9,13][l%4]
 target=4+l if l<=20 else 33+l
 previous=3 if l==0 else (4+l-1 if l-1<=20 else 33+l-1)
 links.extend([(previous*16+11,a),(a+1,target*16+12),(a+1,target*16)])
assert len(links)==136
# Both source endpoint validations have no error on this no-input body.
def counts(xs):
 p={};c={}
 for a,b,*_ in xs:
  assert a<1024 and b<1024
  assert p.get(a,0)<2;p[a]=p.get(a,0)+1
  assert c.get(b,0)<2;c[b]=c.get(b,0)+1
 return max(p.values()),max(c.values())
legacy_counts=counts(legacy);forest_counts=counts(links)
rust=(R/copy).read_text().split('const MASK_LINKS:',1)[1].split('= [',1)[1].split('];',1)[0]
assert links==[tuple(map(int,m)) for m in re.findall(r'\((\d+),\s*(\d+)\)',rust)]
lean=(D/'lean/PV_B3_Forest_134_Funs.lean').read_text().split('Array.make 136#usize [',1)[1].split(']',1)[0]
assert links==[tuple(map(int,m)) for m in re.findall(r'\((\d+)#u16,\s*(\d+)#u16\)',lean)]
original=[0]*64;copied=[0]*64
for row in sorted({x for pair in links for x in pair}):original[row>>4]|=1<<(row&15)
for pair in links:
 for row in pair:copied[row>>4]|=1<<(row&15)
assert original==copied
# Full files pin constants, imports, type definitions and helper call closure.
files={p:sha((R/p).read_bytes()) for p in [forest,tree,profile,copy]}
out=dict(kind='STRUCTURAL argument under ruling (k); not a machine proof',row='V230',op=134,
 source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),files=files,
 reviewed_control_tokens_sha256=sha(pinfile.read_bytes()),original_links=127,forest_links=136,
 legacy_endpoint_max=legacy_counts,forest_endpoint_max=forest_counts,table_matches_emission=True,
 all_error_paths='Shape counts and helper Options succeed; both endpoint passes succeed on the frozen no-input constructors; producer before consumer rejection order retained',
 deliberate_differences=[dict(change='schedule replaced by frozen MASK_LINKS',check='all 136 ordered endpoint pairs equal the pinned constructor trace'),
 dict(change='sort_unstable and dedup omitted; marks interleaved with validation',check='same endpoints; no error is reachable; OR commutes, associates and is idempotent',lean=['PV_B3_Close134.or_idempotent','PV_B3_Close134.or_commutative','PV_B3_Close134.or_associative','PV_B3_MaskDictionary134.copy_reference']),
 dict(change='u8 increment split into Option bump',check='0/1 increment; >=2 rejects before increment',lean=['PV_B3_MaskSparseStep.step','PV_B3_MaskRowExpected.op134_value'])],
 native_link_evidence_class='structural source argument + extraction; native sample is finite validation',
 native_validation='mask-fidelity-comparison.json (same-input, no input arguments, original/copy/emission 64 masks)',
 universal_native_machine_equality_claimed=False,XR_imports=False)
(D/'STRUCTURAL134-D336.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
