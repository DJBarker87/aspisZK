#!/usr/bin/env python3
"""PCXQ: PIN2_R0_REPORT.json. Per function of the r0 module: verdict, receipts, NEW_GATE shas."""
import re,json,hashlib,subprocess,sys
sys.dont_write_bytecode=True
src=open('PCXQ_fndiff.py').read();exec(src[:src.index('res=dict(')])
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
F=FILES[0]
newsrc=show(NEW,F);its=items(newsrc)
def rust_fn(name,chain_sub=None):
    c=[i for i in its if i['kind']=='fn' and i['name']==name and (chain_sub is None or chain_sub in i['chain'])]
    assert len(c)==1,(name,len(c));return c[0]
D='PCXQ_E001_emitted/raw/PCXQ_r0/'
funs=open(D+'Funs.lean').read()
def blocks(s):
    out={}
    for p in re.split(r'(?m)^(?=/-- \[)',s)[1:]:
        m=re.search(r'(?m)^def\s+(\S+)',p)
        if m:out[m.group(1)]=p.rstrip('\n')
    return out
B=blocks(funs);strip=lambda b:re.sub(r"(?m)^\s*Source: .*$",'',b)
P='pool_v1.pair_forest_semantic_terminal.'
rows=[]
def row(emit,rustname,chain,verdict,receipt,extra=None):
    r=dict(emitted=emit,rust=rustname,verdict=verdict,receipt=receipt)
    if emit in B:r['emitted_block_sha256_without_source_line']=sha(strip(B[emit]))
    if rustname:
        f=rust_fn(rustname,chain);r['rust_source_text_sha256_normalized']=sha(norm(f['text']));r['rust_source_lines_new']=f['line']
    if extra:r.update(extra)
    rows.append(r)
EQ='PCXQ_L001 exit 0 (PRVEq_PB_w4.lean; theorem PRVEq.AspisR1PublicPreparation.Funs_w1.%s; axioms propext, Classical.choice, Quot.sound)'
row('aspis_core.field.P',None,None,'unchanged-equal',EQ%'aspis_core.field.P')
for e,rn in [(P+'r0.Public.public_bytes.fields_loop.body','fields'),(P+'r0.Public.public_bytes.fields_loop','fields'),(P+'r0.Public.public_bytes.fields','fields'),(P+'r0.Public.public_bytes.frontier','frontier')]:
    row(e,None,None,'unchanged-equal',EQ%e,dict(rust_note='closure/loop of '+rn+' nested in Public::public_bytes; Rust text of the nested fns is inside the changed public_bytes item; the emitted block is text-identical (modulo Source line numbers) to the 4bb3b3f emission'))
for e,rn,ch in [(P+'private_public','private_public',None),(P+'withdrawal_public','withdrawal_public',None),(P+'r0.Public.public_bytes','public_bytes','r0')]:
    row(e,rn,ch,'changed-new-gate','PIN2_NEWGATE_r0.lean, PCXQ_L004 exit 0')
row(P+'r0.Public.semantic','semantic','r0','unchanged-text-but-depends-on-changed (NEW_GATE)','Rust text unchanged and the emitted body is identical modulo Source line numbers; fresh = gate is not stated because Public.semantic constructs and returns SemanticPublic (type gained destination : Option (Array U8 32)) through the changed private_public/withdrawal_public. PIN2_NEWGATE_r0.lean, PCXQ_L004 exit 0')
out=dict(schema='PIN2_R0_REPORT/1',target_established=False,source_old=OLD,source_new=NEW,
 source_file=F,source_file_sha256=hashlib.sha256(newsrc.encode()).hexdigest(),source_file_git_blob='0b33c09310798c62264c8e56a566bc436b853862',source_tree_git_hash='ab33a923c2b50acdefe256308ec8aee8018b0be4',
 tool='second tool version: Charon 454586e9 (sha256 57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851) + Aeneas 0d21a9ec (sha256 230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91)',
 tool_choice='original Aeneas 959659a6 not used: retired for this root by PCVL_E002 (Aeneas Failure on SemanticPublic variants) and PCVL_E004 (Not_found), the shape is unchanged; see PCXQ_CLASSIFICATIONS.json',
 configuration='overflow-checks ON (RUSTFLAGS -C overflow-checks=yes), release, features r0,pool-v1-kernel + nine pool-v1-pair-forest audit features; start-from r0::Public::public_bytes; --include aspis_core::field::P; cargo --jobs 4 + CARGO_BUILD_JOBS=4; rustc -Zthreads=1; identity by class receipt PCWE_E003',
 extraction_receipt=dict(run='PCXQ_E001',exit=0,wall_seconds=42.1,peak_rss_kib=882132,swaps=0,scope_caps='MemoryHigh=3G MemoryMax=4G MemorySwapMax=0 TasksMax=64, timeout 180 s'),
 emission_files={'Types.lean':sha(open(D+'Types.lean','rb').read()),'Funs.lean':sha(open(D+'Funs.lean','rb').read())},
 new_gate_file='PIN2_NEWGATE_r0.lean',new_gate_file_sha256=sha(open('PIN2_NEWGATE_r0.lean','rb').read()),
 equalities_file='PRVEq_PB_w4.lean',equalities_file_sha256=sha(open('PRVEq_PB_w4.lean','rb').read()),
 functions=rows,
 other_r0_module_functions_not_in_this_emission=dict(names=['transition','terminal_qm31','terminal','terminal_values'],text_changed=False,note='Rust text unchanged, not reached from the public_bytes root, so not emitted here; not checked by this job. transition and terminal_qm31 mention SemanticPublic (type-dependent, see type_dependent_unchanged).'),
 type_dependent_unchanged=json.load(open('PCXQ_type_dependent_unchanged.json')))
json.dump(out,open('PIN2_R0_REPORT.json','w'),indent=1)
for r in rows:print(r['verdict'][:30],'|',r['emitted'].replace(P,''),'|',r.get('emitted_block_sha256_without_source_line','')[:12],r.get('rust_source_text_sha256_normalized','')[:12])
print(out['new_gate_file_sha256'],out['emission_files'])
