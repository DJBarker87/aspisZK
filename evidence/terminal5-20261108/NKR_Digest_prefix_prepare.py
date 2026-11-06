from pathlib import Path
import subprocess,re,json,hashlib,difflib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';old=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_Digest_prefix_split.rs.txt').read_text()
a=old.index('fn public_digest_packed_selector_tensor(');a=old.index('{',a)+1;b=old.index('    let source = public.transition.live_snapshot;',a);prefix=old[a:b]
compact=lambda s:re.sub(r'\s+','',s)
checks=[('anchor','left_digest_packed_selector_tensor','selectors.high[56],openings.z,public.anchor','NKR_Digest_pstep_left'),('nullifier','left_digest_packed_selector_tensor','selectors.high[26],openings.z,public.nullifier','NKR_Digest_pstep_left'),('recipient','optional_recipient_packed_selector_tensor','public.recipient,openings.z,selectors.high[29]','NKR_Digest_pstep_recipient'),('change','left_digest_packed_selector_tensor','selectors.high[32],openings.z,public.change','NKR_Digest_pstep_left')]
parts={}
for n,orig,args,new in checks:
 pat=r'let '+n+r'\s*=\s*'+orig+r'\((.*?)\);';m=re.search(pat,prefix,re.S);assert m,n
 assert compact(m.group(1).rstrip().rstrip(','))==compact(args),n
 assert new+'('+args+',l)' in compact(code),n
 for j in range(2):assert compact(f'local_sums[1][{j}]=local_sums[1][{j}].add({n}[{j}]);') in compact(prefix)
 parts[n]=dict(original_call=m.group(0),scope='one actual child and two adds on arbitrary3x2prestate',identity=True)
assert 'local_sums[1][0]=NKR_Digest_pstep_add(local_sums[1][0],child[0],l);' in compact(code)
assert 'local_sums[1][1]=NKR_Digest_pstep_add(local_sums[1][1],child[1],l);' in compact(code)
name='crates/aspis-statement/src/pool_v1/NKR_Digest_prefix_split.rs';newsource=old+'\n#[cfg(kani)]\n#[path="NKR_Digest_prefix_split.rs"]\nmod NKR_Digest_prefix_split;\n';patch=''.join(difflib.unified_diff(old.splitlines(True),newsource.splitlines(True),fromfile='a/'+source,tofile='b/'+source))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name));(E/'NKR_Digest_prefix_split.patch').write_text(patch)
(E/'NKR_Digest_PREFIX_STEP_ERASURE.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),parts=parts,full_input_domain=True,flat_primitive_input=True,retired=['K018inputunwindfailure','K034whole12eventprefixTIMEOUT'],caps_unchanged=True,timeout_unchanged=True),indent=1));print('NKR prefix fouractualsites→one arbitrary-prestate3event step identity PASS')
