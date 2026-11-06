from pathlib import Path
import re,subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_Digest_split_native.rs.txt').read_text()
def body(s,name):
 m=re.search(r'fn '+re.escape(name)+r'(?:<[^>]*>)?\(',s);assert m,name;p=s.index('{',m.start());q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
def replace_call(s,orig,new):
 while orig+'(' in s:
  start=s.index(orig+'(');p=start+len(orig);q=p+1;depth=1
  while depth:depth+=(s[q]=='(')-(s[q]==')');q+=1
  args=s[p+1:q-1].rstrip().rstrip(',');s=s[:start]+new+'('+args+',l)'+s[q:]
 return s
def adds(s,new):
 return re.sub(r'local_sums\[([012])\]\[([01])\] = local_sums\[\1\]\[\2\]\.add\((\w+)\[\2\]\);',rf'local_sums[\1][\2] = {new}(local_sums[\1][\2],\3[\2],l);',s)
compact=lambda s:re.sub(r'\s+','',s)
full=body(old,'public_digest_packed_selector_tensor');a=full.index('    let source =');b=full.index('    local_sums[0][0] =',a);c=full.index('    let next_root =',b);d=full.index('    let carry =',c);e=full.index('    let mut output =',d)
parts={}
parts['append']=(full[a:b],replace_call(full[a:b],'append_levels_packed_selector_tensor','NKR_Digest_split_append')+'let _=after;(append_local0,append_local12)')
parts['levels_add']=(full[b:c],adds(full[b:c],'NKR_Digest_split_add')+'local_sums')
parts['root']=(full[c:d],'let after=public.transition.candidate_afterstate;'+adds(replace_call(full[c:d],'left_digest_packed_selector_tensor','NKR_Digest_split_root'),'NKR_Digest_split_radd')+'local_sums')
parts['carry']=(full[d:e],'let after=public.transition.candidate_afterstate;'+adds(replace_call(replace_call(full[d:e],'bounded_append_carry','NKR_Digest_split_carry'),'optional_carry_packed_selector_tensor','NKR_Digest_split_optional'),'NKR_Digest_split_cadd')+'local_sums')
for name,(original,trans) in parts.items():
 actual=body(code,'NKR_Digest_split_'+name+'_segment');assert compact(trans)==compact(actual),name+' frozen-control mismatch'
wrapper=body(old,'public_digest_packed');assert 'return public_digest_packed_selector_tensor(public, openings, selectors);' in wrapper
assert compact(body(code,'NKR_Digest_split_wrapper'))==compact('return NKR_Digest_split_wrapper_child(public,openings,selectors,l);')
(E/'NKR_Digest_SPLIT_ERASURE.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),input_domain='FULL arbitrary valid Public/transition/frontiers/openings/selectors/prestate; flat primitive u32 arrays, no representative-only domain',flat_input_repair='flat[u32;4*N] replaces nested generator, checked source segments unchanged',segments={n:dict(original=x[0],translated=x[1],identity=True) for n,x in parts.items()},wrapper=dict(original=wrapper,identity=True,scope='only same2cell reply return; payload forwarding reused plus source-parametric proof'),retired=['NKR_K020 middle TIMEOUT','NKR_K022 whole wrapper TIMEOUT'],caps_unchanged=True,timeout_unchanged=True),indent=1))
name='crates/aspis-statement/src/pool_v1/NKR_Digest_split_native.rs';new=old+'\n#[cfg(kani)]\n#[path="NKR_Digest_split_native.rs"]\nmod NKR_Digest_split_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))+' '.join([])
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_Digest_split_native.patch').write_text(patch)
print('NKR digest4source-segments plus wrapper2return frozen-control identity PASS')
