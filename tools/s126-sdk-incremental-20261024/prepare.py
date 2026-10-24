#!/usr/bin/env python3
"""Prepare ONLY new raw declaration closure over the immutable released base."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'sdk-current-incremental-20261024'
P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
release=json.loads((E/'sdk-current-export-20261024/release.json').read_text());base=Path(release['location']);manifest=json.loads((base/'manifest.json').read_text());assert sha(base/'manifest.json')==release['manifest_sha256']
rows=[json.loads(line) for line in (base/'constants.jsonl').read_text().splitlines()]
names=sorted(set(r['name'] for r in rows));assert len(names)==manifest['constant_count']==27287
old=json.loads((E/'sdk-current-export-20261024/input-pins-v2.json').read_text());old_files={r['module']:{Path(f['path']).name:f['sha256'] for f in r['files']} for r in old['inputs']}
new=json.loads((E/'s1-sdk-challenge-ranges-import-pins.json').read_text());inputs=[]
for row in new['modules']:
 p=Path(row['path']);assert sha(p)==row['sha256'];files=[]
 for suffix in ['', '.server','.private']:
  f=Path(str(p)+suffix)
  if f.exists():
   h=sha(f);files.append(dict(path=str(f),sha256=h,bytes=f.stat().st_size))
   if row['name'] in old_files:assert old_files[row['name']][f.name]==h,(row['name'],f)
 if row['name'] in old_files:assert {Path(f['path']).name for f in files}==old_files[row['name']].keys()
 inputs.append(dict(module=row['name'],files=files))
# New compiled modules supplement the base; no unchanged payload is reserialized.
modules=['S6SdkSourceCutTypesV1','S6SdkSourceCutReuseV1','S6SdkEnclosingCutsV1','S1SdkSourceCutNumericV1','S6SdkFirstObjectEquivalenceV1','S6SdkOriginalObjectCallerV1','S1SdkPreparedChallengeRangesV1']
seeds=['AspisR1.AdapterRw.LeadInputs.Public','AspisR1.S2W_NativeConsolidation.FirstCut','AspisR1.S2W_NativeConsolidation.SecondCut','AspisR1.S2W_NativeConsolidation.SourceCuts','AspisS6SdkSourceCutReuse.bytes_injective','AspisS6SdkSourceCutReuse.same_inputs','AspisS6SdkSourceCutReuse.source_cut_reuse','AspisS6SdkEnclosingCuts.accepted_sdk_all_cuts','AspisS1ValuesOwnedInstallation.sdk_stage1_source_cut_numeric','AspisS6SdkFirstObjectEquivalence.originalFirst','AspisS6SdkFirstObjectEquivalence.first_eq_original','AspisS6SdkOriginalObjectCaller.original_sdk_all_cuts','AspisS6SdkOriginalObjectCaller.original_sdk_source_cut_numeric','AspisS1SdkPreparedChallengeRanges.original_sdk_prepared_claim_trace_ranges']
w=Path('/private/tmp/s126-sdk-current-incremental-20261024-v1');w.mkdir(mode=0o700,exist_ok=False);(w/'transport').mkdir(mode=0o700)
roots=json.loads((E/'s1-sdk-prepared-challenge-ranges-v1/receipt.json').read_text())['lean_path'].split(':')
config=dict(schema='focused-extractor-proof-packet-v1',roots=roots,modules=modules,seeds=seeds,all_declarations=[],baseline_names=names,dest=str(w/'transport'))
(P/'input.json').write_text(json.dumps(config,indent=2)+'\n');(w/'input.json').write_bytes((P/'input.json').read_bytes())
(P/'input-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),inputs=inputs,baseline_manifest_sha256=release['manifest_sha256'],baseline_location=str(base),baseline_constants_sha256=sha(base/'constants.jsonl'),baseline_names=names,base_inputs_checked_unchanged=True,original_helper_pins='s6-sdk-source-cuts-20261024/equivalence-input-binding.json',scope='Incremental UNTRUSTED data, complete new type/opaque value/constructor/mutual/recursor closure over the hash-pinned immutable base. Not kernel replay or source/runtime/native/release closure.'),separators=(',',':'))+'\n')
request_path='docs/research/100bit-spend-path-20261013/design/HANDOFF-SESSION-A-20261021.md';request=subprocess.check_output(['git','show','06d6684215:'+request_path])
(P/'request.json').write_text(json.dumps(dict(revision='06d6684215',path=request_path,sha256=hashlib.sha256(request).hexdigest(),requested_modules=modules[:-1],additional_new_checked_target=modules[-1],scope='Incremental CURRENT export requested by lead; original-side/kernel join remains lead-owned; reserved lead attempts untouched.'),indent=2)+'\n')
print(json.dumps(dict(work=str(w),input_modules=len(inputs),base_constants=len(names),seeds=len(seeds))))
