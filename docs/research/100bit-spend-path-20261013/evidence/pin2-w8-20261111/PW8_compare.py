#!/usr/bin/env python3
"""PW8 step 3: fresh (PW8_E002, PIN2 pair, c7593d23fdc) = gate comparison, declaration by declaration, against the frozen
release-gate AspisR1PublicPreparation.{Types,Funs} (L187 source, read-only copies passed by path and checked by sha256),
plus the identity check of the fresh public_bytes / public_transcript closure against the overlay PIN2_NEWGATE_r0 /
PIN2_NEWGATE_r1_semantic (STOP if any same-name declaration differs).
Classes: identical (PW8_lib.norm tokens equal, fresh side PCXU xform only) / tool-option adaptation (equal after
PW8_toolmap.TOOL_MAP on the gate side; entries listed) / changed-new-gate (text differs and the difference is the PIN2
source change, or text equal but the declaration uses a changed declaration transitively) / not-in-fresh-scope (gate
declaration from the mirror crate that the PIN2 roots do not reach) / fresh-only.
usage: python3 PW8_compare.py <gate Types.lean> <gate Funs.lean> <overlay PIN2_NEWGATE_r0.lean> <overlay PIN2_NEWGATE_r1_semantic.lean> [PW8_E004]"""
import sys,re,json
sys.dont_write_bytecode=True
from PW8_lib import *
from PW8_toolmap import TOOL_MAP,apply_tool_map
GT,GF,N0,N1=sys.argv[1:5]
PIN={GT:'b45ee7357278642101b81933252e81f5068c937487acfdebb4f82f991c91bb83',GF:'544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d',
     N0:'949d0070883f92f9ae9a0a49c57c165a1feec4a430334602f2897471f61488bd',N1:'b0a096b056f8c68bf64832a97cb1c65c5d09e771eca992304ee9ef75c7390fc6'}
for p,h in PIN.items():assert sha(open(p,'rb').read())==h,('input drift',p)
RUN=sys.argv[5] if len(sys.argv)>5 else 'PW8_E004'  # E004 = E002 + root types Verified, SecureCirclePoint (all shared declarations token-identical to E002)
R=RUN+'_emitted/raw/PW8_vp/'
fresh={};order=[]
for f in ['Types.lean','Funs.lean']:
    for b in blocks(xform(inner(open(R+f).read(),'PW8_vp'))):fresh[key(b)]=b;order.append(key(b))
ext=open(R+'FunsExternal_Template.lean').read();externals=re.findall(r'(?m)^axiom (\S+)',ext)
gate={};gorder=[]
for p in [GT,GF]:
    for b in gate_split(inner(open(p).read(),'AspisR1PublicPreparation')):k=key(b);assert k,b[:120];gate[k]=strip_disc(b);gorder.append(k)
RENAME={'aspis_core.Digest32':'aspis_core.digest.Digest32','r1_wire.Challenges':'aspis_core.state_only_prefix.r0.Challenges'}
EXPECTED_SOURCE_CHANGE={'pool_v1.pair_forest_semantic_terminal.SemanticPublic':'type gains field destination : Option (Array U8 32) (pair_forest_semantic_terminal.rs:97-99 at c7593d23fdc)',
 'pool_v1.pair_forest_semantic_terminal.private_public':'sets destination := none',
 'pool_v1.pair_forest_semantic_terminal.withdrawal_public':'sets destination := some public.destination_token_account',
 'pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes':'appends pool, deployment_domain, has_destination byte, destination iff present (both variants)'}
def refs(text,names):
    return {n for n in names if re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])',re.sub(r'(?s)^/--.*?-/\n','',text))}
rows=[];stop=[];changed=set()
for k in gorder:
    fk=RENAME.get(k,k)
    if fk not in fresh:rows.append(dict(declaration=k,cls='not-in-fresh-scope'));continue
    a0=norm(gate[k]);b=norm(fresh[fk]);used=set();a1=norm(apply_tool_map(gate[k],used))
    if a0==b:rows.append(dict(declaration=k,cls='identical'))
    elif a1==b:rows.append(dict(declaration=k,cls='tool-option adaptation',fresh_name=fk if fk!=k else None,tool_map=[TOOL_MAP[i][2] for i in sorted(used)]+([ 'renamed path (see RENAME)'] if fk!=k else [])))
    elif k in EXPECTED_SOURCE_CHANGE:rows.append(dict(declaration=k,cls='changed-new-gate',reason=EXPECTED_SOURCE_CHANGE[k]));changed.add(k)
    else:rows.append(dict(declaration=k,cls='STOP: unexplained difference'));stop.append(k)
# transitive closure: unchanged text that uses a changed declaration (type or callee) is a new-gate constant too
names=set(gate)
while True:
    new=set()
    for r in rows:
        k=r['declaration']
        if k in changed or r['cls'] not in ('identical','tool-option adaptation'):continue
        hit=refs(fresh[RENAME.get(k,k)],changed)
        if hit:r['transitive_via']=sorted(hit);r['text_class']=r['cls'];r['cls']='changed-new-gate (transitive; text '+r['cls']+')';new.add(k)
    if not new:break
    changed|=new
# not-in-fresh-scope reasons
def nreason(k):
    if 'Insts.CoreFmtDebug' in k or 'Insts.CoreCmp' in k or 'Insts.CoreClone' in k or 'Insts.CoreMarker' in k or 'assert_fields_are_eq' in k:return 'mirror-crate derive (Debug/PartialEq/Eq/Clone/Copy impl); not reached from the PIN2 roots'
    if k.startswith('pool_v1.pair_forest_terminal.'):return 'mirror-crate fragment terminal_statement/terminal_common; not reached from the PIN2 roots'
    if k.startswith(('verifier.','aspis_core.r0.','aspis_core.field.WideExact')):return 'mirror-crate tx1/verifier carrier (gate tail "Exact newly emitted declarations"); not reached from the PIN2 roots'+('; in VerifyPrefix it is replaced by RPz7_PhaseIso.Phase (RPz7 swap)' if k=='verifier.Phase' else '')
    if k.startswith(('transcript.','transport.')):return 'mirror-crate fragment transcript_type/transcript_new/transcript_step/compiled_variant tag; not reached from the PIN2 roots'
    if k=='r1_wire.sample_validated_entry':return 'mirror-crate helper; not reached from the PIN2 roots'
    if k=='core.result.Result.map_err':return 'library item: second tool resolves it in the Aeneas library; PIN2 model is PCWN_NewLib.core.result.Result.map_err (in PIN2_NEWGATE_r1_semantic, HM-C)'
    if k=='Array.Insts.CoreCmpPartialEqArray':return 'library trait impl used only by mirror-crate PartialEq derives'
    return 'not reached from the PIN2 roots'
for r in rows:
    if r['cls']=='not-in-fresh-scope':r['reason']=nreason(r['declaration'])
covered={RENAME.get(r['declaration'],r['declaration']) for r in rows}
fresh_only=[]
for k in order:
    if k in covered:continue
    used_by=sorted(j for j in fresh if j!=k and refs(fresh[j],{k}))
    fresh_only.append(dict(declaration=k,referenced_by=used_by,note=('trait impl instance whose method is an external axiom in FunsExternal_Template; referenced by no fresh declaration' if 'CoreCloneClone' in k else '')))
# identity of the public_bytes / public_transcript closure against the overlay PIN2 NEWGATE files
ng={};src={}
for p,tag in [(N0,'PIN2_NEWGATE_r0'),(N1,'PIN2_NEWGATE_r1_semantic')]:
    for k,b in gate_blocks(p).items():ng[k]=b;src[k]=tag
newgate=[]
for k in order:
    if k in ng:
        eq=norm(ng[k])==norm(fresh[k]);newgate.append(dict(declaration=k,in_file=src[k],token_identical=eq))
        if not eq:stop.append('NEWGATE mismatch: '+k)
counts={}
for r in rows:c=r['cls'].split(' (')[0];counts[c]=counts.get(c,0)+1
res=dict(schema='PW8_COMPARISON/1',fresh=RUN,fresh_sha256={f:sha(open(R+f,'rb').read()) for f in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},
 gate_sha256={'Types.lean':PIN[GT],'Funs.lean':PIN[GF]},overlay_sha256={'PIN2_NEWGATE_r0.lean':PIN[N0],'PIN2_NEWGATE_r1_semantic.lean':PIN[N1]},
 counts=counts,stop=stop,gate_declarations=rows,fresh_only=fresh_only,fresh_externals=externals,newgate_identity=newgate,
 tool_map=[dict(pattern=p,replacement=r,reason=w) for p,r,w in TOOL_MAP],renames=RENAME)
json.dump(res,open('PW8_COMPARISON.json','w'),indent=1,ensure_ascii=False)
with open('PW8_COMPARISON.tsv','w') as f:
    f.write('declaration\tclass\tdetail\n')
    for r in rows:f.write('%s\t%s\t%s\n'%(r['declaration'],r['cls'],r.get('reason') or ('via '+','.join(r['transitive_via']) if r.get('transitive_via') else '') or '; '.join(r.get('tool_map',[]))))
print(json.dumps(counts),'stop',stop);print('fresh_only',[(x['declaration'],x['referenced_by']) for x in fresh_only]);print('externals',externals)
print('newgate',[(x['declaration'],x['in_file'],x['token_identical']) for x in newgate])
print('changed',sorted(k for k in changed))
