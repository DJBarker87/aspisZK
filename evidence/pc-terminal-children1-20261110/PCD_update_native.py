from pathlib import Path
import json,difflib,subprocess,hashlib
E=Path(__file__).resolve().parent
p=E/'PCD_lane_native.rs';s=p.read_text().replace('kani::any::<[u32;8]>().map(aspis_core::field::M31)', '['+','.join(['aspis_core::field::M31(kani::any())']*8)+']');p.write_text(s)
meta=json.loads((E/'PCD_NATIVE_PATCH_META.json').read_text());meta['suffix']='\n#[cfg(kani)]\n#[allow(non_snake_case)]\nmod PCD_harness {\n    use super::*;\n'+s+'\n}\n'
source=subprocess.check_output(['git','show','b936275465600469312d1f058cdc91ea2a11f3dc:'+meta['source']],text=True);start=source.index('fn next_pair_forest_lane_v1(');modified=source[:start]+meta['annotation']+source[start:]+meta['suffix'];meta['modified_sha256']=hashlib.sha256(modified.encode()).hexdigest()
(E/'PCD_NATIVE_PATCH_META.json').write_text(json.dumps(meta,indent=1)+'\n');(E/'PCD_native_packets.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),modified.splitlines(True),fromfile='a/'+meta['source'],tofile='b/'+meta['source'])))
p=E/'PCD_NATIVE_REPAIR_FILES.json';files=json.loads(p.read_text());files['PCD_src/'+meta['source']]=modified;files['PCD_NATIVE_PATCH_META.json']=json.dumps(meta,indent=1)+'\n';p.write_text(json.dumps(files,indent=1)+'\n')
p=E/'PCD_native_run.py';s=p.read_text().replace("if a=='PCD_K005':args+=['--unwind','1','--verbose']","if a in ['PCD_K005','PCD_K006','PCD_K002']:args+=['--unwind','1','--verbose']");p.write_text(s)
p=E/'PCD_NATIVE_REPAIRS.md';s=p.read_text();s+='\nK005 reaches CBMC and FAILS on array::map input-constructor unwinding (loop 0, bound 1), not on the target contract. Repair input construction to eight explicit arbitrary M31 fields, preserving the exact unrestricted input domain while removing the constructor loop and function-pointer argument. No unwind increase, assertion removal or renamed target. K006 keeps the same contract/harness name and bound 1.\n';p.write_text(s)
print('PCD native input constructor split into explicit arbitrary fields; frozen-body erasure is unchanged.')
