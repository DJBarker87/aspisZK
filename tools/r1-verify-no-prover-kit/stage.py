#!/usr/bin/env python3
"""Stage immutable Git-exact source + declared10 test/tool overlays. No builds."""
import argparse,difflib,hashlib,importlib.util,io,json,subprocess,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--after',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();dest=a.out.resolve();assert not dest.exists(),dest
 s=importlib.util.spec_from_file_location('prepare',HERE/'prepare.py');prep=importlib.util.module_from_spec(s);s.loader.exec_module(prep);declared=json.loads((HERE/'source-pins.json').read_text());overlay,pins=prep.build(a.after,declared.get('source_scope','all'));assert len(overlay)==(3 if pins.get('source_scope')=='counter' else 10);assert declared==pins
 arpath='docs/research/100bit-spend-path-20261013/evidence/final-a555-clean-native-20261017/final-a555-clean-native.tar.gz';raw=prep.git('6dd9028e9',arpath);t=tarfile.open(fileobj=io.BytesIO(raw));files={};originals={};matched=[]
 for n in t.getmembers():
  if not n.name.startswith('source-clean/') or not n.isfile():continue
  name=n.name[len('source-clean/'):];assert name and not name.startswith('/') and '..' not in Path(name).parts;b=t.extractfile(n).read();originals[name]=b
  if name in pins['fixture_files']:assert sha(b)==pins['fixture_files'][name]
  assert prep.git(pins['after_revision'],name)==b,('source/fixture differs from Git',name);matched.append({'path':name,'sha256':sha(b),'pinned_fixture':name in pins['fixture_files']})
  files['source/'+name]=b
 assert len(matched)==532,('baseline source universe changed',len(matched))
 deltas={}
 for name,b in overlay.items():
  before=originals.get(name,b'');deltas[name]={'before_Git_or_absent_sha256':sha(before),'after_sha256':sha(b),'was_in_Git_source_universe':name in {i['path'] for i in matched},'diff':''.join(difflib.unified_diff(before.decode().splitlines(True),b.decode().splitlines(True),fromfile='Git234/'+name,tofile='test-tool-overlay/'+name))};files['source/'+name]=b
 for name in pins['fixture_files']:
  files['fixtures/'+Path(name).name]=originals[name]
 files['baseline-ordered-counter.json']=t.extractfile('ordered-counter.json').read()
 for path in HERE.iterdir():
  if path.is_file() and path.suffix in ['.py','.json','.md']:files['tools/r1-verify-no-prover-kit/'+path.name]=path.read_bytes()
 files['tools/r1-native-feature-audit/audit.py']=(ROOT/'tools/r1-native-feature-audit/audit.py').read_bytes()
 audit={'classification':'STRICT_STAGED_INPUT_AUDIT_NO_BUILD','source_revision':pins['after_revision'],'baseline_archive_path':arpath,'baseline_archive_sha256':sha(raw),'Git_exact_source_files':matched,'Git_exact_source_count_including_two_fixtures':len(matched),'fixture_files':pins['fixture_files'],'declared_test_tool_overlays':deltas,'overlay_count':len(deltas),'source_pins_sha256':sha((HERE/'source-pins.json').read_bytes()),'uncompiled_c5_material_included':False,'new_native_jobs':0,'all_source_changes_declared':True}
 files['source-audit.json']=(json.dumps(audit,sort_keys=True,indent=2)+'\n').encode()
 inputs={'source_revision':pins['after_revision'],'source_kind':'Git-exact accepted532 source universe +10 explicit test/tool overlays +pinned fixtures; no production worktree changes','files':{n:sha(b) for n,b in sorted(files.items())},'production_source_audit_sha256':sha(files['source-audit.json']),'source_pins_sha256':sha((HERE/'source-pins.json').read_bytes()),'gate_labels':[g['label'] for g in pins['gates']]}
 files['inputs.json']=(json.dumps(inputs,sort_keys=True,indent=2)+'\n').encode()
 for name,b in files.items():path=dest/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b)
 assert len(list((dest/'source').rglob('*')))>=len(matched)
 print(json.dumps({'status':'PASS_STRICT_STAGE_NO_BUILD','source_revision':pins['after_revision'],'Git_exact_source_files':532,'declared_overlays':len(deltas),'input_manifest_sha256':sha(files['inputs.json']),'input_files':len(inputs['files']),'source_audit_sha256':sha(files['source-audit.json']),'out':str(dest)},sort_keys=True))
if __name__=='__main__':main()
