#!/usr/bin/env python3
"""Read-only NUC cache inventory: correlate root Cargo fingerprint dependency IDs to exact cached artifacts."""
import json, pathlib, re
root=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/target/release')
fp_path=root/'.fingerprint/charon-dce94fe66085d37d/bin-charon-driver.json'
fp=json.loads(fp_path.read_text())
rows=[]
for dep_id,name,_public,dep_hash in fp['deps']:
    file_name='lib-'+name.replace('-','_')+'.json'
    matches=[]
    for meta_path in root.joinpath('.fingerprint').glob('*/'+file_name):
        directory=meta_path.parent.name
        marker=meta_path.with_suffix('')
        # remove only final .json suffix; this is Cargo's sibling lib-<crate> fingerprint marker.
        marker=meta_path.parent/('lib-'+name.replace('-','_'))
        if not marker.is_file():
            continue
        marker_text=marker.read_text().strip()
        try:
            marker_num=int.from_bytes(bytes.fromhex(marker_text),"little")
        except ValueError:
            marker_num=None
        try:
            meta=json.loads(meta_path.read_text())
        except Exception as e:
            meta={'parse_error':str(e)}
        artifact_prefix='lib'+name.replace('-','_')+'-'+directory.rsplit('-',1)[-1]
        artifacts=[]
        for path in root.joinpath('deps').glob(artifact_prefix+'.*'):
            if path.suffix in ('.rlib','.rmeta','.so','.d'):
                st=path.stat()
                artifacts.append({'path':str(path.relative_to(root)),'size':st.st_size,'mode':oct(st.st_mode & 0o777)})
        matches.append({'fingerprint_dir':directory,'marker_text':marker_text,'marker_int':marker_num,'matches_expected_id':marker_num==dep_hash,'meta_file':str(meta_path.relative_to(root)),'features':meta.get('features'),'profile':meta.get('profile'),'target':meta.get('target'),'artifact_candidates':artifacts})
    rows.append({'cargo_dep_id':dep_id,'name':name,'fingerprint_hash_u64':dep_hash,'matches':matches})
print(json.dumps({'fingerprint_source':str(fp_path),'dependency_count':len(rows),'deps':rows},indent=2,sort_keys=True))
