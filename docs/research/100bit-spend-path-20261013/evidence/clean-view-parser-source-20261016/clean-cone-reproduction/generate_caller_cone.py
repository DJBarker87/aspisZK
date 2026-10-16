from pathlib import Path
import hashlib,json
root=Path('/tmp/r1-viewparse-clean-models-20261016');out=root/'AspisR1ViewParseProbe'
raw=Path('/tmp/r1-view-parse-echeck-cut-20261016/attempt-h-owned-offset-shape/output/generated/AspisR1ViewParseProbe/Funs.lean')
s=raw.read_text();original=s;removed=[]
for name in ['verifier.view_parse_probe','verifier.View.parse']:
 defstart=s.index('def '+name+'\n');start=s.rfind('/-- ',0,defstart);assert start>=0
 ends=[p for p in [s.find('\n/-- ',start),s.find('\nend AspisR1ViewParseProbe',start)] if p!=-1]
 end=min(ends);segment=s[start:end];removed.append({'name':name,'text':segment,'sha256':hashlib.sha256(segment.encode()).hexdigest()});s=s[:start]+s[end:]
s=s.replace('import AspisR1ViewParseProbe.FunsExternal','import AspisR1ViewParseProbe.CallerStdModels')
# Removed declaration spans include their own source documentation comments.
(out/'CallerFuns.lean').write_text(s)
p=Path('/tmp/r1-view-parse-echeck-cut-20261016/parameterized-parse-attempt-c/ParameterizedParse.lean')
pbody=p.read_text();assert pbody.count('import AspisR1ViewParseProbe.Funs\n')==1
clean=pbody.replace('import AspisR1ViewParseProbe.Funs\n','import AspisR1ViewParseProbe.CallerFuns\n')
(out/'CleanParameterizedParse.lean').write_text(clean)
# Reverse the declaration cuts by their original raw offsets, not guessed placement.
restored=s.replace('import AspisR1ViewParseProbe.CallerStdModels','import AspisR1ViewParseProbe.FunsExternal')
for entry in reversed(removed):
 pos=original.index(entry['text'])
 # All prior removed declarations lie later in the source than this one.
 restored=restored[:pos]+entry['text']+restored[pos:]
assert restored==original
assert clean.replace('import AspisR1ViewParseProbe.CallerFuns\n','import AspisR1ViewParseProbe.Funs\n')==pbody
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest={'raw_generated_sha256':sha(raw.read_bytes()),'removed_declarations':removed,'retained_source_reconstruction_exact':True,'parameterized_source_sha256':sha(p.read_bytes()),'parameterized_import_only_change':True,'std_models_boundary':'Explicit pinned Rust/Aeneas library models; no opaque query helper/global axiom in retained cone','files':{str(f.relative_to(root)):sha(f.read_bytes()) for f in out.glob('*.lean')},'generator_sha256':sha(Path(__file__).read_bytes())}
(root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest['files'],indent=2))
