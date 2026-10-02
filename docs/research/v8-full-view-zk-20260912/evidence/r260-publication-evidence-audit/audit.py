import copy,hashlib,json,pathlib,re
BASE=pathlib.Path('docs/research/v8-full-view-zk-20260912');EVID=BASE/'evidence'
R259=EVID/'r259-current-private-input-raw';R260=EVID/'r260-current-private-input-execution'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def axiom_lines(text):
    lines=text.splitlines();out=[];i=0
    while i<len(lines):
        if lines[i].startswith("'") and ' depends on axioms: [' in lines[i]:
            block=[lines[i]]
            while ']' not in block[-1]:
                i+=1
                if i>=len(lines):raise AssertionError('truncated axiom output')
                block.append(lines[i])
            out.append(' '.join(' '.join(block).split()))
        elif lines[i].startswith("'") and ' does not depend on any axioms' in lines[i]:out.append(' '.join(lines[i].split()))
        i+=1
    return out
reports=[]
for slug,p,want_ax,want_no_ax,want_reject in [
 ('r259-current-private-input-raw',R259,6,1,1),
 ('r260-current-private-input-execution',R260,6,2,1)]:
    m=json.loads((p/'manifest.json').read_text());sums=json.loads((p/'SHA256SUMS.json').read_text());bad=[]
    for rel,h in sums.items():
        q=p/rel
        if not q.is_file():bad.append('missing:'+rel)
        elif sha(q)!=h:bad.append('hash:'+rel)
    actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q!=p/'SHA256SUMS.json'}
    unlisted=sorted(actual-set(sums));stale=sorted(set(sums)-actual)
    target=BASE/'lean'/m['target'];src=p/'source'/pathlib.Path(m['target']).name
    source_match=target.is_file() and src.is_file() and target.read_bytes()==src.read_bytes() and sha(src)==m['source_sha256']
    if not source_match:bad.append('target-source-copy-hash-mismatch')
    log=(p/m['log']).read_text(errors='replace'); observed=axiom_lines(log);expected=[' '.join(x.split()) for x in m['complete_print_axioms']]
    if observed!=expected:bad.append('complete-axiom-log-mismatch')
    axfile=(p/'axioms.txt').read_text()
    if axfile!='\n'.join(m['complete_print_axioms'])+'\n':bad.append('axioms-file-mismatch')
    noax=sum('does not depend on any axioms' in x for x in expected)
    if len(expected)!=want_ax or noax!=want_no_ax:bad.append('axiom-count-mismatch')
    allowed={'propext','Classical.choice','Quot.sound'};foundations=True
    for x in expected:
        if 'does not depend on any axioms' in x:continue
        fs=set(re.findall(r'propext|Classical\.choice|Quot\.sound|sorryAx|native_decide',x))
        if fs-allowed or not fs:foundations=False
    if not foundations or 'sorryAx' in log:bad.append('unexpected-axiom-or-sorryAx-in-good-log')
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',log);rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',log);sw=re.search(r'Swaps: (\d+)',log);ex=re.search(r'Exit status: (\d+)',log)
    metrics=bool(wall and rss and sw and ex and wall.group(1)==m['wall_time'] and int(rss.group(1))==m['peak_rss_kib'] and int(sw.group(1))==m['swaps'] and int(ex.group(1))==m['exit_status']==0)
    if not metrics:bad.append('success-log-metrics-mismatch')
    res=m['resources'];runner=(p/'run_focus.py').read_text()
    caps=all(s in runner for s in [f"MemoryHigh={res['MemoryHigh']}",f"MemoryMax={res['MemoryMax']}",f"MemorySwapMax={res['MemorySwapMax']}",f"TasksMax={res['TasksMax']}",'systemd-run']) and all(s in runner for s in res['flags'].split())
    target_flags=pathlib.Path(m['target']).name in log and all(s in log for s in res['flags'].split())
    if not caps:bad.append('caps-runner-mismatch')
    if not target_flags:bad.append('target-flags-log-mismatch')
    rejected=[]
    for f in sorted((p/'rejected').glob('*.log')):
        t=f.read_text(errors='replace');status=re.search(r'Exit status: (\d+)',t)
        rejected.append({'log':str(f.relative_to(p)),'exit_status':int(status.group(1)) if status else None,'sorryAx_present':'sorryAx' in t})
    if len(rejected)!=want_reject or any(x['exit_status']!=1 or not x['sorryAx_present'] for x in rejected):bad.append('rejected-draft-status-or-sorryAx-mismatch')
    note=BASE/('R259_CURRENT_PRIVATE_INPUT_RAW.md' if 'r259' in slug else 'R260_CURRENT_PRIVATE_INPUT_EXECUTION.md');nt=note.read_text()
    note_ok=all(v in nt for v in [m['source_revision'],m['wall_time'],str(m['peak_rss_kib']),str(m['swaps'])]) and 'Full callback chronology, joint privacy and soundness remain open.' in nt
    if not note_ok:bad.append('note-metrics-or-scope-mismatch')
    reports.append({'bundle':slug,'target':m['target'],'source_revision':m['source_revision'],'source_sha256':m['source_sha256'],'exit_status':m['exit_status'],'wall_time':m['wall_time'],'peak_rss_kib':m['peak_rss_kib'],'swaps':m['swaps'],'checksum_count':len(sums),'checksum_errors':bad,'unlisted_files':unlisted,'stale_checksum_entries':stale,'target_copy_exact':source_match,'axiom_reports':len(expected),'axiom_free_reports':noax,'complete_log_axioms_match':observed==expected,'foundation_only_or_no_axioms':foundations,'success_log_metrics_exact':metrics,'runner_caps_exact':caps,'target_and_flags_logged':target_flags,'rejected_logs':rejected,'scope_note_checked':note_ok,'manifest_boundary':m['proved_boundary']})
    assert not bad and not unlisted and not stale,(slug,bad,unlisted,stale)
# Audit saved R255/R256 chain without replay.
R245=pathlib.Path('.r21-scratch/r245-r110-leaf-extract/R245R110Leaves.llbc')
R255=R259/'provenance/r255-ordering/R255R110CompleteOrdered.llbc'
R255_audit=json.loads((R259/'provenance/r255-ordering/audit.json').read_text())
assert sha(R245)=='59412a374a2753759103071c7190ac6587249517b0f991e619afc8a12a93e197'
assert sha(R255)=='65d240e27115591fa6dc459e9c4a94785667840cbf1f1deddafc892c764dca88'
old=json.loads(R245.read_text());ordered=json.loads(R255.read_text());o=copy.deepcopy(old);q=copy.deepcopy(ordered);o['translated'].pop('ordered_decls');q['translated'].pop('ordered_decls')
assert o==q and R255_audit['only_changed_json_path']=='translated.ordered_decls' and R255_audit['all_original_declaration_rows_identical'] is True
r256_cmd=json.loads((R259/'provenance/r256-translation/translate-command.json').read_text())
assert r256_cmd['source_sha256']==sha(R255)
F256=R259/'provenance/r256-translation/generated/AspisR256R110CompleteLeaves/Funs.lean'
assert sha(F256)=='de9bc21245ab4305a2565f83ad102f2d6ea87785d06dc194302a879750026efa'
# Byte-compare exactly three selected declaration blocks, not the whole generated file.
NAMES=['core.option.Option.Insts.CoreOpsTry_traitTry.branch','core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual','circle_norm.joined_inverse.line_norm.r110_norm.C.input']
def blocks(text):
    starts=[m.start() for m in re.finditer(r'(?m)^/--',text)];out={}
    for i,start in enumerate(starts):
        end=starts[i+1] if i+1<len(starts) else len(text)
        mark=re.search(r'(?m)^#print axioms ',text[start:end])
        if mark:end=start+mark.start()
        block=text[start:end]
        for name in NAMES:
            pat=r'(?m)^def\s+'+re.escape(name)+r'\s*$|^def\s*$\n\s*'+re.escape(name)+r'\s*$'
            if re.search(pat,block):
                assert name not in out
                out[name]=block.rstrip()+('\n' if block.rstrip() else '')
    assert set(out)==set(NAMES),(set(out),set(NAMES))
    return out
src_blocks=blocks(F256.read_text());out_src=(R259/'source/AspisR259PrivateInputRaw.lean').read_text();raw_blocks=blocks(out_src)
block_checks=[]
for n in NAMES:
    s=src_blocks[n].encode();t=raw_blocks[n].encode();assert s==t,(n,'selected source body block differs')
    block_checks.append({'name':n,'source_sha256':hashlib.sha256(s).hexdigest(),'adapter_sha256':hashlib.sha256(t).hexdigest(),'byte_identical':True})
# Independently verify Option source type row against the retained decoded R245 LLBC row.
D=json.loads(pathlib.Path('.r21-scratch/r245-r110-leaf-extract/decoded.json').read_text())
option=next(x for x in D['translated']['type_decls'] if isinstance(x,dict) and x.get('def_id')==3)
option_copy=json.loads((R259/'provenance/r259-raw/option-type-source.json').read_text())
assert option==option_copy
v=option['kind']['Enum'];tags={row['name']:row['discriminant'] for row in v}
expected_tags={'None':{'Scalar':{'Signed':['Isize','0']}},'Some':{'Scalar':{'Signed':['Isize','1']}}}
assert tags==expected_tags
rowsha=sha(R259/'provenance/r259-raw/option-type-source.json')
binding=json.loads((R259/'provenance/r259-raw/discriminant-binding.json').read_text());assert binding['type_row_sha256']==rowsha and binding['variants']==[[k,v] for k,v in expected_tags.items()]
raw_src=out_src
support_checks={'optionTag_definition_present':bool(re.search(r'def optionTag\s*\{T : Type\} : Option T → Isize\s*\| none => 0#isize\s*\| some _ => 1#isize',raw_src)),'local_discriminant_instance_present':bool(re.search(r'local instance optionDiscriminant\s*\{T : Type\} : Discriminant \(Option T\) Isize where\s*read_discriminant := optionTag',raw_src)),'none_and_some_tag_lemmas_present':'theorem optionTag_none' in raw_src and 'theorem optionTag_some' in raw_src,'tag_type_signed_isize':tags==expected_tags,'r245_option_type_row_exact':option==option_copy}
assert all(support_checks.values())
# Check R255 itself was only order metadata against the full original raw R245 input.
# Option Infallible is mapped to an empty inductive in the retained pinned Convert excerpt.
convert=(R259/'provenance/r259-raw/pinned-Convert.lean').read_text()
infallible_empty=bool(re.search(r'\[rust_type "core::convert::Infallible"\]\s*inductive core\.convert\.Infallible where\s*(?:\n\s*\n|\n\[)',convert))
assert infallible_empty
convert_sha=sha(R259/'provenance/r259-raw/pinned-Convert.lean')
raw_prov=json.loads((R259/'provenance/r259-raw/raw-adapter.json').read_text())
assert raw_prov['pinned_aeneas_source']['sha256']==sha(R259/'provenance/r259-raw/pinned-Discriminant.lean')
assert raw_prov['sha256']['R255_ordered_LLBC']==sha(R255) and raw_prov['sha256']['generated_Funs_lean']==sha(F256)
# Internal R259 provenance sums and top-level sums were checked above; verify nested checksum list too.
inner=[]
for line in (R259/'provenance/r259-raw/SHA256SUMS').read_text().splitlines():
    h,rel=line.split('  ',1);p=pathlib.Path(rel);assert p.is_file() and sha(p)==h,(str(p),h);inner.append(str(p))
assert len(inner)==13
# Confirm R259 documentation labels the addition as discriminator support, not whole-file identity/source proof.
notes=(BASE/'R259_CURRENT_PRIVATE_INPUT_RAW.md').read_text();stage=(R259/'provenance/r259-raw/README.md').read_text()
assert 'Three actual generated Option branch/residual/C::input bodies compile byte-for-byte unchanged' in notes
assert 'named local discriminant instance' in notes and 'Definition compilation is not a whole callback' in notes
assert 'The block byte hashes are equal' in stage and 'lead-approved local Option `Discriminant` support' in stage and 'No body was manually changed' in stage
# R256 translated Funs defines the three functions and uses the generic Infallible type; retained pinned Convert makes it an empty inductive.
assert all(n in F256.read_text() for n in NAMES) and 'core.convert.Infallible' in F256.read_text()
report={'status':'PASS_READ_ONLY_R259_R260_EVIDENCE_AUDIT','audited_at':'2026-10-02','bundles':reports,'r259_generated_block_audit':{'source':'R256 generated Funs.lean','source_sha256':sha(F256),'selected_blocks':block_checks,'selected_block_count':len(block_checks),'only_these_blocks_compared':True,'whole_generated_file_claim':False,'added_discriminant_support':support_checks,'option_type_row_sha256':rowsha,'option_tags':tags,'pinned_Discriminant_excerpt_sha256':convert_sha,'pinned_Convert_Infallible_empty_type_present':infallible_empty,'pinned_Convert_excerpt_sha256':convert_sha,'pinned_convert_excerpt_path':str((R259/'provenance/r259-raw/pinned-Convert.lean').relative_to(EVID))},'r255_r256_chain_audit':{'r245_input_sha256':sha(R245),'r255_sha256':sha(R255),'r255_diff_only_ordered_decls':True,'r255_saved_audit_confirms_only_ordering':True,'r256_input_sha256':r256_cmd['source_sha256'],'r256_input_matches_r255':r256_cmd['source_sha256']==sha(R255),'r256_generated_Funs_sha256':sha(F256)},'r259_nested_checksums_verified':len(inner),'scope':'Saved artifact/evidence consistency only. Three generated R256 declaration blocks were byte-compared; the full generated file was not asserted unchanged. No source proof/security or broader semantic conclusion.'}
out=pathlib.Path('.r21-scratch/r260-publication-evidence-audit/audit.json');out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'bundles':[{'bundle':x['bundle'],'checksums':x['checksum_count'],'axioms':x['axiom_reports'],'axiomfree':x['axiom_free_reports'],'rss':x['peak_rss_kib'],'wall':x['wall_time'],'rejected':x['rejected_logs']} for x in reports],'r259_blocks':block_checks,'support_checks':support_checks,'R255_R256':report['r255_r256_chain_audit'],'Infallible_empty':infallible_empty},indent=2))
