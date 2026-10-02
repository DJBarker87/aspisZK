import hashlib,json,pathlib,re
BASE=pathlib.Path('docs/research/v8-full-view-zk-20260912')
EVID=BASE/'evidence'
SLUGS=['r249-current-private-arithmetic-raw','r250-current-private-base-execution']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sha_text=lambda s:hashlib.sha256(s.encode()).hexdigest()
def axiom_lines(text):
    lines=text.splitlines(); out=[]; i=0
    while i<len(lines):
        line=lines[i]
        if line.startswith("'") and ' depends on axioms: [' in line:
            bits=[line]
            while ']' not in bits[-1]:
                i+=1
                if i>=len(lines):raise AssertionError('truncated axiom output')
                bits.append(lines[i])
            out.append(' '.join(' '.join(bits).split()))
        elif line.startswith("'") and ' does not depend on any axioms' in line:
            out.append(' '.join(line.split()))
        i+=1
    return out
reports=[]
for slug in SLUGS:
    p=EVID/slug;m=json.loads((p/'manifest.json').read_text()); sums=json.loads((p/'SHA256SUMS.json').read_text())
    bad=[]
    for rel,h in sums.items():
        q=p/rel
        if not q.is_file():bad.append('missing:'+rel)
        elif sha(q)!=h:bad.append('hash:'+rel)
    actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q!=p/'SHA256SUMS.json'}
    unlisted=sorted(actual-set(sums));stale=sorted(set(sums)-actual)
    target=BASE/'lean'/m['target'];source=p/'source'/pathlib.Path(m['target']).name
    source_equal=target.is_file() and source.is_file() and target.read_bytes()==source.read_bytes()
    if not source_equal:bad.append('source-copy-mismatch')
    if not source_equal or sha(source)!=m['source_sha256']:bad.append('source-hash-mismatch')
    log=(p/m['log']).read_text(errors='replace'); observed=axiom_lines(log)
    expected=[' '.join(x.split()) for x in m['complete_print_axioms']]
    axioms_match=observed==expected
    if not axioms_match:bad.append('axiom-log-mismatch')
    axfile=(p/'axioms.txt').read_text()
    if axfile!='\n'.join(m['complete_print_axioms'])+'\n':bad.append('axioms-file-mismatch')
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',log)
    rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)
    swaps=re.search(r'Swaps: (\d+)',log);exitm=re.search(r'Exit status: (\d+)',log)
    metrics=bool(wall and rss and swaps and exitm and wall.group(1)==m['wall_time'] and int(rss.group(1))==m['peak_rss_kib'] and int(swaps.group(1))==m['swaps'] and int(exitm.group(1))==m['exit_status']==0)
    if not metrics:bad.append('good-log-metrics-mismatch')
    runner=(p/'run_focus.py').read_text(); resources=m['resources']
    resource_values=[f"MemoryHigh={resources['MemoryHigh']}",f"MemoryMax={resources['MemoryMax']}",f"MemorySwapMax={resources['MemorySwapMax']}",f"TasksMax={resources['TasksMax']}"]
    resource_ok=all(v in runner for v in resource_values) and all(v in runner for v in resources['flags'].split()) and 'systemd-run' in runner
    if not resource_ok:bad.append('resource-runner-mismatch')
    cmdok=pathlib.Path(m['target']).name in log and all(v in log for v in resources['flags'].split())
    if not cmdok:bad.append('target-flags-not-in-log')
    rejected=[]
    rp=p/'rejected'
    if rp.exists():
        for f in sorted(rp.glob('*.log')):
            t=f.read_text(errors='replace'); ex=re.search(r'Exit status: (\d+)',t)
            rejected.append({'log':str(f.relative_to(p)),'exit_status':int(ex.group(1)) if ex else None,'sorryAx_present':'sorryAx' in t})
    allowed={'propext','Classical.choice','Quot.sound'}; ax_foundations=True; noaxiom=[]
    for item in expected:
        if 'does not depend on any axioms' in item:noaxiom.append(item);continue
        found=set(re.findall(r'propext|Classical\.choice|Quot\.sound|sorryAx|native_decide',item))
        if found-allowed or not {'propext','Classical.choice','Quot.sound'}>=found:ax_foundations=False
    if not ax_foundations:bad.append('unexpected-axiom-output')
    note=(BASE/('R249_CURRENT_PRIVATE_ARITHMETIC_RAW.md' if slug.startswith('r249') else 'R250_CURRENT_PRIVATE_BASE_EXECUTION.md')).read_text()
    note_ok=all(v in note for v in [m['source_revision'],m['wall_time'],str(m['peak_rss_kib']),str(m['swaps'])]) and 'Full callback chronology, joint privacy and soundness remain open.' in note
    if not note_ok:bad.append('scope-note-or-metrics-mismatch')
    reports.append({'bundle':slug,'target':m['target'],'source_revision':m['source_revision'],'source_sha256':m['source_sha256'],'exit_status':m['exit_status'],'wall_time':m['wall_time'],'peak_rss_kib':m['peak_rss_kib'],'swaps':m['swaps'],'checksum_count':len(sums),'checksum_errors':bad,'unlisted_files':unlisted,'stale_checksum_entries':stale,'source_matches_target_and_copy':source_equal,'successful_log_axioms_match_manifest':axioms_match,'axiom_report_count':len(expected),'no_axiom_report_count':len(noaxiom),'foundation_only':ax_foundations,'successful_log_metrics_match':metrics,'resource_scope_matches_runner':resource_ok,'target_and_flags_in_log':cmdok,'note_scope_and_metrics_ok':note_ok,'rejected_logs':rejected,'manifest_scope':m['proved_boundary']})
    assert not bad and not unlisted and not stale, (slug,bad,unlisted,stale)
# Independent R249 adapter correspondence check against R247 full generated Funs.
r249=EVID/'r249-current-private-arithmetic-raw'; prov=r249/'provenance/r249-r110-raw'; gen=r249/'provenance/r247-r110-leaf-translation/generated/AspisR247R110Leaves/Funs.lean'; types=r249/'provenance/r247-r110-leaf-translation/generated/AspisR247R110Leaves/Types.lean'; pinned=BASE/'lean/AspisR156FullFreeze/FunsCore.lean'; adapter=r249/'source/AspisR249R110Raw.lean'
def decl_blocks(text,strip_generated_end=False):
    starts=[m.start() for m in re.finditer(r'(?m)^/--',text)]; result={}
    for i,s in enumerate(starts):
        b=text[s:starts[i+1] if i+1<len(starts) else len(text)]
        if strip_generated_end:b=re.sub(r'\nend AspisR247R110Leaves\s*$','',b)
        m=re.search(r'(?m)^def ([\w.]+)',b)
        if m:result[m.group(1)]=b.strip()
    return result
def norm(s):return re.sub(r'\s+',' ',s).strip()
def body(s):return s[s.index('def '):]
generated=decl_blocks(gen.read_text(),True); adapted=decl_blocks(adapter.read_text()); pinblocks=decl_blocks(pinned.read_text()); typeblocks=decl_blocks(types.read_text(),True)
functions=['circle_norm.joined_inverse.line_norm.r110_norm.B.input','circle_norm.joined_inverse.line_norm.r110_norm.B.reduce','circle_norm.joined_inverse.line_norm.r110_norm.B.add','circle_norm.joined_inverse.line_norm.r110_norm.B.sub','circle_norm.joined_inverse.line_norm.r110_norm.B.half','circle_norm.joined_inverse.line_norm.r110_norm.B.mul','circle_norm.joined_inverse.line_norm.r110_norm.C.output','circle_norm.joined_inverse.line_norm.r110_norm.C.add','circle_norm.joined_inverse.line_norm.r110_norm.C.sub','circle_norm.joined_inverse.line_norm.r110_norm.C.half','circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m','circle_norm.joined_inverse.line_norm.r110_norm.C.mul','circle_norm.joined_inverse.line_norm.r110_norm.C.square','circle_norm.joined_inverse.line_norm.r110_norm.C.times_r','circle_norm.joined_inverse.line_norm.r110_norm.C.norm','circle_norm.joined_inverse.line_norm.r110_norm.C.double']
globals_=['circle_norm.joined_inverse.line_norm.r110_norm.P110','circle_norm.joined_inverse.line_norm.r110_norm.C.mul.PP']; selected=[globals_[0]]+functions[:6]+functions[6:11]+[globals_[1]]+functions[11:]
repls=[('core.num.U32.wrapping_add','Std.U32.wrapping_add',2),('core.num.U32.wrapping_sub','Std.U32.wrapping_sub',1),('core.num.U64.wrapping_add','Std.U64.wrapping_add',2),('core.num.U64.wrapping_sub','Std.U64.wrapping_sub',1),('Std.U32.wrapping_shr self 1#i32','Std.U32.wrapping_shr self 1#u32',1),('Std.U32.wrapping_shl i1 30#i32','Std.U32.wrapping_shl i1 30#u32',1),('Std.U64.wrapping_shr x 31#i32','Std.U64.wrapping_shr x 31#u32',1)]
counts={f'{a} -> {b}':sum(generated[n].count(a) for n in functions) for a,b,_ in repls}
assert [counts[f'{a} -> {b}'] for a,b,_ in repls]==[c for _,_,c in repls]
body_results=[]
for n in selected:
    assert n in generated and n in adapted,(n,n in generated,n in adapted)
    expected=generated[n]
    for a,b,_ in repls:expected=expected.replace(a,b)
    equal=norm(body(expected))==norm(body(adapted[n]))
    assert equal,(n,'adapter body differs outside listed substitutions')
    body_results.append({'name':n,'body_matches_after_only_listed_substitutions':True,'generated_body_sha256':sha_text(body(generated[n])),'adapter_body_sha256':sha_text(body(adapted[n]))})
# Generated and adapter aliases B/C.
assert norm(body(typeblocks['circle_norm.joined_inverse.line_norm.r110_norm.B'])).endswith(':= Std.U32')
assert norm(body(typeblocks['circle_norm.joined_inverse.line_norm.r110_norm.C'])).endswith(':= circle_norm.joined_inverse.line_norm.r110_norm.B × circle_norm.joined_inverse.line_norm.r110_norm.B')
adapt_text=adapter.read_text(); alias_checks={'B_alias':bool(re.search(r'@\[reducible\]\s+def circle_norm\.joined_inverse\.line_norm\.r110_norm\.B := Std\.U32',adapt_text)),'C_alias':bool(re.search(r'def circle_norm\.joined_inverse\.line_norm\.r110_norm\.C\s*:=\s*circle_norm\.joined_inverse\.line_norm\.r110_norm\.B ×\s*circle_norm\.joined_inverse\.line_norm\.r110_norm\.B',adapt_text))}
assert all(alias_checks.values())
# Explicit globals are exact, with no source-body substitution.
for n in globals_:assert norm(body(generated[n]))==norm(body(adapted[n]))
external=['aspis_core.field.P','aspis_core.field.reduce_u64','aspis_core.field.M31.reduce_u64','aspis_core.field.CM31.new']
ext_matches={n:n in generated and n in pinblocks and norm(body(generated[n]))==norm(body(pinblocks[n])) for n in external}
assert all(ext_matches.values())
assert all(not re.search(r'(?m)^def '+re.escape(n)+r'\b',adapt_text) for n in external)
assert 'import AspisR156FullFreeze.FunsCore' in adapt_text and 'open AspisR156FullFreeze' in adapt_text
# Ensure adapter local generated bodies are exactly selected 18 plus B/C and count lemmas.
local_names=set(re.findall(r'(?m)^\s*(?:@\[[^\]]+\]\s*)?def ([\w.]+)',adapt_text)) | set(re.findall(r'(?m)^\s*theorem ([\w.]+)',adapt_text))
expected_local=set(selected)|{'circle_norm.joined_inverse.line_norm.r110_norm.B','circle_norm.joined_inverse.line_norm.r110_norm.C','count_one','count_thirty','count_thirty_one'}
assert local_names==expected_local,(local_names-expected_local,expected_local-local_names)
# Binding audit input hashes and substitution counts cross-check source identities.
ba=json.loads((prov/'binding-audit.json').read_text())
for rel,h in ba['input_sha256'].items():assert sha(pathlib.Path(rel))==h,(rel,h,sha(pathlib.Path(rel)))
assert ba['output_sha256']['AspisR249R110Raw.lean']==sha(adapter)
inner=[]
for line in (prov/'binding-audit.SHA256SUMS').read_text().splitlines():
    h,rel=line.split('  ',1); q=pathlib.Path(rel); assert q.is_file() and sha(q)==h,(rel,h);inner.append(rel)
assert len(inner)==8
adapter_report={'selected_functions':len(functions),'selected_globals':len(globals_),'selected_definitions_exact_body_match':len(body_results),'body_matches':body_results,'replacement_counts':counts,'replacement_only_verification':True,'global_P110_PP_exact':True,'B_C_aliases_match':alias_checks,'external_R156_exact_bindings':ext_matches,'no_local_external_shadow_defs':True,'generated_selected_declaration_count':len(selected),'local_declaration_set_exact':True,'binding_audit_inputs_verified':len(ba['input_sha256']),'binding_audit_internal_checksums_verified':len(inner),'excluded_C_input_absent_from_adapter':not re.search(r'(?m)^\s*def circle_norm\.joined_inverse\.line_norm\.r110_norm\.C\.input\b',adapt_text)}
assert adapter_report['excluded_C_input_absent_from_adapter']
# R250 rejected drafts must have exit status 1 and are retained with README.
r250=EVID/'r250-current-private-base-execution';rejects=[]
for f in sorted((r250/'rejected').glob('*.log')):
    t=f.read_text(errors='replace'); ex=re.search(r'Exit status: (\d+)',t)
    rejects.append({'log':str(f.relative_to(r250)),'exit_status':int(ex.group(1)) if ex else None,'sorryAx_present':'sorryAx' in t})
assert len(rejects)==2 and all(x['exit_status']==1 and x['sorryAx_present'] for x in rejects)
report={'status':'PASS_READ_ONLY_EVIDENCE_AUDIT','audited_at':'2026-10-02','bundles':reports,'r249_adapter_exact_substitution_audit':adapter_report,'r250_rejected_drafts':rejects,'scope':'Saved evidence consistency only. No source-semantics, runtime, cryptographic, or security decision is made. No builds/regressions or tracked edits.'}
out=pathlib.Path('.r21-scratch/r250-publication-evidence-audit/audit.json');out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'bundles':[{'bundle':r['bundle'],'checksums':r['checksum_count'],'axioms':r['axiom_report_count'],'no_axioms':r['no_axiom_report_count'],'metrics':r['successful_log_metrics_match'],'resource_scope':r['resource_scope_matches_runner'],'rejects':len(r['rejected_logs'])} for r in reports],'adapter':adapter_report,'r250_rejected_drafts':rejects},indent=2))
