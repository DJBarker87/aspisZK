from pathlib import Path
import hashlib,json,shutil
own=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016');old=own/'lean';new=own/'lean-bridge'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
new.mkdir(exist_ok=True);(new/'sources').mkdir(exist_ok=True);(new/'objects').mkdir(exist_ok=True)
for rel in ['AspisR1PrefixAggregateParser/Funs.lean','ExtractedPrefixRecordStep.lean','ExtractedPrefixTrace.lean','ExtractedPrefixParse.lean','ExtractedPrefixFieldAgreement.lean']:
 src=old/'sources'/rel;dest=new/'sources'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
for rel in ['AspisR1RecordParser/Types','AspisR1RecordParser/Funs']:
 for folder,ext in [('sources','.lean'),('objects','.olean')]:
  src=old/folder/(rel+ext);dest=new/folder/(rel+ext);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
shutil.copytree(old/'record-cache-provenance',new/'record-cache-provenance',dirs_exist_ok=True)
m=json.loads((old/'input-manifest.json').read_text());m.pop('new_sources',None);m.pop('new_import_objects',None)
m['isolated_naming_adapter']={'original_workspace':str(old),'no_original_prefix_objects_reused':True,'generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03'}
(new/'input-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(new)
