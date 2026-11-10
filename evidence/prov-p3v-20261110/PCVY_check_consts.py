#!/usr/bin/env python3
"""PCVY: compare NCV_Reference.EMPTY / BINDING (reference crate, Aeneas-extracted) with the frozen Rust text at 4bb3b3f (read via git show)."""
import re,subprocess,json,sys
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def show(p): return subprocess.check_output(['git','show',F+':'+p],text=True)
roots=show('programs/aspis-verifier/src/v7_pair_empty_roots.rs')
body=roots.split('V7_PAIR_EMPTY_ROOTS')[1].split('= [',1)[1]
body=re.sub(r'//[^\n]*','',body)
nums=[int(x.replace('_','')) for x in re.findall(r'M31::new\(\s*([0-9_]+)|\b([0-9][0-9_]{4,})\b',body) for x in x if x]
ref=open(sys.argv[1]).read()
e=ref.split('def EMPTY',1)[1].split('/-- [ncv_reference::equal]',1)[0]
refn=[int(x) for x in re.findall(r'(\d+)#u32',e)]
b=ref.split('def BINDING',1)[1].split('/--',1)[0]
refb=[int(x) for x in re.findall(r'(\d+)#u8',b)]
res=dict(frozen_numeric_literals=len(nums),reference_words=len(refn),roots_equal=(nums[:168]==refn and len(nums)>=168),first=nums[:3],refirst=refn[:3])
# binding from frozen: ASPISFOREST8, versions, lane count, digest enc, depth, 1, zeros
fb=show('crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs').split('POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING: [u8; 32] = [',1)[1].split('];',1)[0]
fb=re.sub(r'//[^\n]*','',fb)
toks=[t.strip() for t in fb.split(',') if t.strip()]
env={'POOL_V1_PAIR_FOREST_MASTER_VERSION':None,'POOL_V1_PAIR_FOREST_LANE_VERSION':2,'POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION':2,'POOL_V1_PAIR_FOREST_LANE_COUNT as u8':8,'POOL_V1_DIGEST_ENCODING_VERSION':1,'POOL_V1_TREE_DEPTH as u8':20}
res['binding_tokens']=toks
res['binding_ref']=refb
print(json.dumps(res))
