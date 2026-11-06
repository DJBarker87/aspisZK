from pathlib import Path
import subprocess,json,hashlib,difflib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
s=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_TermPrefix_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;d=1
 while d:d+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
compact=lambda s:re.sub(r'\s+','',s)
b=body(s,'composition_parts');pre=b[:b.index('    let openings =')]
expected='''let invalid_amount = match public.withdrawal_amount {None => false,Some(amount) => amount == 0 || amount >= (1 << 30u32),};
if invalid_amount {return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);}
validate_transition(public)?;'''
assert compact(pre)==compact(expected),'Frozen validation prefix changed'
translated='''let invalid_amount=match public.withdrawal_amount{None=>false,Some(amount)=>amount==0||amount>=(1<<30u32)};
if invalid_amount{return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);}
NKR_prefix_validate(public,l)?;
Ok(true)'''
assert compact(body(code,'NKR_validation_prefix'))==compact(translated)
assert 'core::array::from_fn(|i|claims[i/28][i%28])' in compact(body(s,'terminal_qm31')),'Frozen gather callback changed'
assert compact(body(code,'NKR_terminal_gather_cell'))=='claims[i/28][i%28]'
name='crates/aspis-statement/src/pool_v1/NKR_TermPrefix_native.rs';new=s+'\n#[cfg(kani)]\n#[path="NKR_TermPrefix_native.rs"]\nmod NKR_prefix_native;\n'
patch=''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name));(E/'NKR_TermPrefix_native.patch').write_text(patch)
(E/'NKR_TermPrefix_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(s.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),frozen_prefix=pre,translated=translated,identity=True,shapes=['NKR_validation_prefix_cut','NKR_terminal_gather_cell_cut'],scope='237 complete actual amount/validation Result prefix;256onearbitrary gathercallback, finite frame/induction required, not whole84buffer'),indent=2))
print('237validation and256gather frozen windows PASS')
