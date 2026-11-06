from pathlib import Path
import json,hashlib,subprocess,re,difflib
p=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';name='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';s=subprocess.check_output(['git','show',rev+':'+name],text=True);compact=lambda t:re.sub(r'\s+','',t)
anchors=['Selectors::boxed_at_point(point)','poseidon_selectors(&selectors)','PreparedQm31Multiplier::new(theta)','selected_claim(claims, 0, SELECTED_H1_COLUMN)','selected_claim(claims, 0, SELECTED_G_COLUMN)','copy_variant(public.variant)','composition_parts(public, claims, point, lambda, chi, theta)?']
for a in anchors:assert compact(a) in compact(s),a
old=s
mods={'TermSemantic':'NKR_term_semantic_native','TermScalarWindows':'NKR_scalar_windows_native','TermPrefix':'NKR_prefix_native','TermHorner':'NKR_horner_native','Forward':'NLH_forward_native','Composition':'NLH_composition_native'}
for f,m in mods.items():old+='\n#[cfg(kani)]\n#[path="NLH_'+f+'_native.rs"]\nmod '+m+';\n'
new=old
for f,m in [('Leaves','NLH_leaves_native'),('Parts','NLH_parts_native')]:new+='\n#[cfg(kani)]\n#[path="NLH_'+f+'_native.rs"]\nmod '+m+';\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name,tofile='b/'+name));pins=json.loads((p/'NLH_SOURCE_PINS.json').read_text());pins[name]=hashlib.sha256(new.encode()).hexdigest()
for f in ['Leaves','Parts']:
 code=(p/('NLH_'+f+'_native.rs.txt')).read_text();target='crates/aspis-statement/src/pool_v1/NLH_'+f+'_native.rs';patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+target));pins[target]=hashlib.sha256(code.encode()).hexdigest()
(p/'NLH_extend.patch').write_text(patch);(p/'NLH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(p/'NLH_EXTEND_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,frozen_source=name,anchors=anchors,identity=True,windows=['237 selector argument/full80-field Box value','237 poseidon-selector argument/full block+16 local result','237 constructor theta/cache','237 actual selected H1/G columns','237 actual copy-variant enum','263 complete237 argument/Result full6-channel tuple'],scope='Returning arms and source-side abort prefixes under(an); actual child models substituted in Lean. No endpoint premise or new trust.'),indent=2)+'\n');print('Remaining237/263 frozen call anchors validated')
