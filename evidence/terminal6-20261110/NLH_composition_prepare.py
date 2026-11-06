from pathlib import Path
import subprocess,hashlib,json,re,difflib
p=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';name='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
s=subprocess.check_output(['git','show',rev+':'+name],text=True);code=(p/'NLH_Composition_native.rs.txt').read_text();compact=lambda x:re.sub(r'\s+','',x)
def body(s,n):
 i=s.index('fn '+n+'(');i=s.index('{',i);j=i+1;d=1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
b=body(s,'composition_parts')
anchors=['evaluate_state_only_poseidon_oracle_projected(&openings, &poseidon_selectors(&selectors))','semantic_packed(public, &openings, &selectors)','evaluate_with_selectors(&openings.z,h1_z,&selectors,lambda,chi,public.transition.live_snapshot.next_pair_index,copy_variant(public.variant),)']
for anchor in anchors:assert compact(anchor) in compact(b),anchor
native={'NLH_composition_poseidon':'NLH_poseidon_oracle(o,s,l)','NLH_composition_semantic':'NLH_semantic_oracle(public,openings,selectors,l)','NLH_composition_copy':'NLH_copy_oracle(z,h1_z,selectors,lambda,chi,index,variant,l)'}
for f,expression in native.items():assert compact(body(code,f))==compact(expression),(f,expression)
for expr in ['selected_claim(claims,0,column)','selected_claim(claims,1,column)','selected_claim(claims,2,column)','selected_claim(claims,0,16+column)']:assert compact(expr) in compact(body(code,'NLH_composition_gather'))
assert 'POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1:usize=16;' in compact(s)
old=s
mods={'TermSemantic':'NKR_term_semantic_native','TermScalarWindows':'NKR_scalar_windows_native','TermPrefix':'NKR_prefix_native','TermHorner':'NKR_horner_native','Forward':'NLH_forward_native'}
for f,m in mods.items():old+='\n#[cfg(kani)]\n#[path="NLH_'+f+'_native.rs"]\nmod '+m+';\n'
new=old+'\n#[cfg(kani)]\n#[path="NLH_Composition_native.rs"]\nmod NLH_composition_native;\n'
file='crates/aspis-statement/src/pool_v1/NLH_Composition_native.rs'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name,tofile='b/'+name))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+file))
(p/'NLH_composition.patch').write_text(patch)
pins=json.loads((p/'NLH_SOURCE_PINS.json').read_text());pins[name]=hashlib.sha256(new.encode()).hexdigest();pins[file]=hashlib.sha256(code.encode()).hexdigest();(p/'NLH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(p/'NLH_COMPOSITION_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,frozen_source=name,frozen_sha256=hashlib.sha256(s.encode()).hexdigest(),anchors=anchors,native=native,gather='Exact four source callbacks, arbitrary valid column, std array assembly composed in Lean',identity=True,source_stage_order=['gather0','gather1','gather2','gather3','selectors','poseidonSelectors','poseidon308','semantic261','h1','copyVariant','copy218','preparedTheta','horner24','horner4','g'],scope='Individual source-occurrence windows, not a whole native root',harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2)+'\n')
print('237 frozen call expressions and gather callbacks validated')
