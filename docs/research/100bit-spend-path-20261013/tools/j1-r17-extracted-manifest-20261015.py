#!/usr/bin/env python3
"""Reproduce source-only Lean 4.32 port inventory. Does not build or select objects."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, tarfile
ROOT = Path(__file__).resolve().parents[4]
BASE = '36ffab8f825cf8ec9ff8dbf57e23195a8e242bdf'
ORIGINAL_BASE = 'b8760b76ac8de6c5c903eb98ff3a85f6f9f532e8'
R = 'docs/research/100bit-spend-path-20261013'
OUT = ROOT / R / 'design/J1-R17-EXTRACTED-MANIFEST-20261015.json'
CANDIDATE = 'ExtractedPublicCheckedBridge432'
CANDIDATE_PATH = R+'/lean/'+CANDIDATE+'.lean'
CANDIDATE_SHA = 'd3067f7d0f28384cbc2e907c8cf438cc6295191174aa8624750308df36b43ab1'
PRIMARY = ['PublicSerializerFieldsRefinement431', 'PublicSerializerSuccess431',
 'PublicSerializerFrontier431', 'PublicSerializerWhole431', 'PublicRawCore',
 'PublicExtractedRawBridge431', 'PublicRawAmountGuard', 'WithdrawalValidationAmount431',
 'WithdrawalCarrierBridge431', 'ExtractedRowShape', 'ExtractedRecordFraming',
 'ExtractedRecordLimbCanonicality', 'ExtractedRecordByteCanonicality',
 'ExtractedRecordHighZero', 'ExtractedRecordValidator', 'RecordPayloadPartition',
 'ExtractedRecordPayloadSoundness', 'PublicRawCoreAgreement', 'PublicRawAmountGuardAgreement']
MASK = ['ExtractedMaskArrayThree','ExtractedMaskCM31Mul','ExtractedMaskM31AddSub',
 'ExtractedMaskPreparedClosure','ExtractedMaskPreparedComponent','ExtractedMaskPreparedMul',
 'ExtractedMaskPreparedState','ExtractedMaskQM31Equality','ExtractedMaskQM31Exact',
 'ExtractedMaskQM31Mul','ExtractedMaskQM31Tower','ExtractedMaskReducer',
 'ExtractedMaskReducerOps','ExtractedMaskTowerAdd']
CURRENT = ['ExtractedCurrentCM31Mul','ExtractedCurrentM31AddSub','ExtractedCurrentQM31Equality',
 'ExtractedCurrentQM31Exact','ExtractedCurrentQM31Mul','ExtractedCurrentQM31Tower',
 'ExtractedCurrentReducer','ExtractedCurrentReducerOps','ExtractedCurrentTowerAdd']
GEN_ROOTS = {
 'AspisR1PublicSerializer': R+'/evidence/lean-public-serializer-source-20261015/AspisR1PublicSerializer',
 'AspisR1WithdrawalValidation': R+'/evidence/withdrawal-validation-source-431-20261015/extraction/attempt-c-fixed-digest/generated/AspisR1WithdrawalValidation',
 'AspisR1RowShape': R+'/evidence/record-parser-local-extraction-20261015/row-shape-a-20261015/generated/AspisR1RowShape',
 'AspisR1RecordParser': R+'/evidence/record-parser-local-extraction-20261015/parse-record-f-header-array-20261015/generated/AspisR1RecordParser',
 'AspisR1Qm31ArithmeticProbe': R+'/evidence/current-qm31-arithmetic-20261015/extraction/attempt-a/generated/AspisR1Qm31ArithmeticProbe'}
EXPLICIT = {ns+'.'+part: path+'/'+part+'.lean' for ns,path in GEN_ROOTS.items() for part in ['Types','Funs']}
EXPLICIT.update({'AspisR1SelectedMaskProbe.'+part: R+'/evidence/current-selected-mask-extraction-20261015/mask-'+part.lower()+'-a.source.lean' for part in ['Types','Funs']})
PURE = ['AspisV8R15.ExactTowerBase','AspisV8R17.RawReducerNat','AspisV8R17.QM31WordFormulas',
 'AspisV8R17.QM31WordResidues','AspisV8R17.QuadraticTowerOperations','AspisV8R17.QM31WordTower']
EXTERNAL = ('Aeneas','Mathlib','Std','Lean','Init','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','Plausible')

def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git','-C',str(ROOT),*args])
def source(path):
    b=(ROOT/path).read_bytes()
    if path == CANDIDATE_PATH:
        if sha(b) != CANDIDATE_SHA: raise ValueError('Candidate differs from pinned proposal: '+path)
    elif b != git('show',BASE+':'+path): raise ValueError('Source differs from pinned base: '+path)
    return b

def uncomment(text):
    # Preserve newlines while skipping nested Lean block comments and line comments.
    out=[];depth=0;i=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;out.extend('  ');i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;out.extend('  ');i+=2
        elif depth:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i);j=len(text) if j<0 else j;out.extend(' '*(j-i));i=j
        else:out.append(text[i]);i+=1
    return ''.join(out)

def imports(b):
    return re.findall(r'^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)',uncomment(b.decode()),re.M)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true')
    ap.add_argument('--stage',type=Path,help='Copy only pinned .lean sources to a new source staging root; never objects or builds')
    a=ap.parse_args()
    tracked=git('ls-tree','-r','--name-only',BASE).decode().splitlines()
    tracked.append(CANDIDATE_PATH)
    canonical=[p for p in tracked if p.endswith('.lean') and p.startswith('docs/research/') and '/evidence/' not in p and '/tools/' not in p]
    def resolve(m):
        if m in EXPLICIT:return EXPLICIT[m]
        if m.startswith('R1') and '.' not in m:
            p=R+'/lean/'+m[2:]+'.lean'
            if p in tracked:return p
        p=R+'/lean/'+m+'.lean'
        if p in tracked:return p
        if m.startswith('AspisV8'):
            p='docs/research/v8-full-view-zk-20260912/lean/'+m.replace('.','/')+'.lean'
            if p in tracked:return p
        suffix='/'+m.replace('.','/')+'.lean';hits=[p for p in canonical if p.endswith(suffix)]
        if len(hits)==1:return hits[0]
        raise ValueError('Unresolved or ambiguous import '+m+': '+repr(hits))
    modules={};external=set();order=[];visiting=set()
    def visit(m):
        if m.split('.')[0] in EXTERNAL:external.add(m);return
        if m in modules:return
        if m in visiting:raise ValueError('Import cycle '+m)
        visiting.add(m);path=resolve(m);b=source(path);imps=imports(b)
        for imp in imps:visit(imp)
        visiting.remove(m)
        role='uncompiled_composition' if m==CANDIDATE else 'generated' if m in EXPLICIT else 'retained_pure' if m in PURE else 'recent_proof' if m in PRIMARY+MASK+CURRENT else 'r1_432_dependency'
        ownership='selected-mask owner; compile-only unchanged input' if m in MASK or m.startswith('AspisR1SelectedMaskProbe.') else 'current-QM31 owner; optional compile-only unchanged input' if m in CURRENT or m.startswith('AspisR1Qm31ArithmeticProbe.') else 'retained algebra; compile-only unchanged input' if m in PURE else 'J1.a/b proof port; no source edit authorized by this inventory'
        if m==CANDIDATE:ownership='worker B new composition proposal; UNCOMPILED'
        modules[m]={'source':path,'source_sha256':sha(b),'git_blob':git('hash-object',path).decode().strip(),'source_revision': 'UNCOMPILED candidate pinned by SHA256' if m==CANDIDATE else BASE,'imports':imps,'role':role,'ownership':ownership,'stage_as':m.replace('.','/')+'.lean','prior_object_selected':False}
        order.append(m)
    groups={}
    for group,targets in [('j1ab_primary',PRIMARY),('final_public_bridge',[CANDIDATE]),('selected_mask_prepared',MASK),('current_qm31_optional_precursor',CURRENT)]:
        for m in targets:visit(m)
        def closure(m,seen):
            if m not in modules or m in seen:return
            seen.add(m)
            for i in modules[m]['imports']:closure(i,seen)
        needed=set()
        for m in targets:closure(m,needed)
        groups[group]={'targets':targets,'order':[m for m in order if m in needed],'optional':group.endswith('precursor')}
    # Cross-check the selected-mask compile closure against accepted archive sources.
    archive=R+'/evidence/current-mask-prepared-20261015/proofs.tar.gz';ab=source(archive);archive_matches=[]
    with tarfile.open(ROOT/archive) as t:
        for m in ['AspisR1SelectedMaskProbe.Types','AspisR1SelectedMaskProbe.Funs']+PURE+MASK:
            member='sources/'+m.replace('.','/')+'.lean';b=t.extractfile(member).read()
            assert sha(b)==modules[m]['source_sha256'],m
            archive_matches.append({'module':m,'member':member,'sha256':sha(b)})
    pins={p:sha(source(p)) for p in ['AspisFormal/lean-toolchain','AspisFormal/lake-manifest.json','AspisFormal/lakefile.toml']}
    extraction_dirs={
      'serializer':R+'/evidence/public-serializer-local-extraction-20261015/frontier-c-enums-20261015',
      'withdrawal':R+'/evidence/withdrawal-validation-source-431-20261015/extraction/attempt-c-fixed-digest',
      'row_shape':R+'/evidence/record-parser-local-extraction-20261015/row-shape-a-20261015',
      'parser':R+'/evidence/record-parser-local-extraction-20261015/parse-record-f-header-array-20261015',
      'current_qm31_optional':R+'/evidence/current-qm31-arithmetic-20261015/extraction/attempt-a'}
    origin_pins={}
    for label,d in extraction_dirs.items():
        paths=[p for p in tracked if p.startswith(d+'/') and (p.endswith('.llbc') or p.endswith('/source-pins.json') or p.endswith('/source-manifest.json') or p.endswith('/tool-pins.json'))]
        origin_pins[label]={'directory':d,'pins':{p:sha(source(p)) for p in paths},'action':'Copy retained source/extraction evidence only; no re-extraction authorized'}
    for part in ['Types','Funs']:
        original=extraction_dirs['serializer']+'/generated/AspisR1PublicSerializer/'+part+'.lean'
        assert sha(source(original))==modules['AspisR1PublicSerializer.'+part]['source_sha256']
    mask_extraction=R+'/evidence/current-selected-mask-extraction-20261015/extraction.tar.gz'
    origin_pins['selected_mask']={'extraction_archive':mask_extraction,'extraction_sha256':sha(source(mask_extraction)),'proof_archive':archive,'proof_sha256':sha(ab),'source_member_prefix':'sources/','exclude_member_prefixes':['objects/'],'action':'Compile-only source dependencies owned by selected-mask worker; no edits/re-extraction'}
    backend_pin_path=R+'/evidence/lean-public-serializer-source-20261015/pins.json'
    historical_backend=json.loads(source(backend_pin_path))['cached_backend']
    data={'format':2,'source_base':BASE,'original_task_base':ORIGINAL_BASE,'review':'c441facae60f957472b4b87180babcda4051eca3','state':'source-only inventory; candidate UNCOMPILED; no extracted-module 4.32 port result','target_toolchain':source('AspisFormal/lean-toolchain').decode().strip(),'workspace_pins':pins,'modules':modules,'topological_order':order,'groups':groups,'external_import_boundary':sorted(external),'accepted_archive_crosscheck':{'path':archive,'sha256':sha(ab),'members':archive_matches},'extraction_evidence_for_host_copy':origin_pins,'historical_backend_source_reference':{'evidence':backend_pin_path,'evidence_sha256':sha(source(backend_pin_path)),'recorded_backend':historical_backend,'status':'Historical 4.31 evidence only; coordinator must pin/rebuild or attest one compatible 4.32 backend and dependency closure. No backend object selected.'},'object_policy':{'accepted_existing_objects':[],'forbidden':'All retained4.31 oleans/private/server/IR, even when source hashes match; historical object archives are evidence only.','reuse_432_requires':['exact Lean4.32 binary/runtime identity','exact source hash','all direct and transitive dependency hashes/toolchains','matching private/server/IR companions if required'],'build_search_path':'Only new4.32 target objects, rebuilt Aeneas4.32 and coordinator-attested single4.32 dependency environment; never old4.31 cache roots.'},'final_gate':{'new_target':CANDIDATE,'status':'UNCOMPILED candidate; no proof claimed','imports':modules[CANDIDATE]['imports'],'fixed_projection':'PublicRawCoreAgreement.fromCore (RawBridge431.project p)','serializer_contract':'PublicSourceBoundary.SourceSerializerRefines RawBridge431.ExtractedReturns projectRaw','composition':['WithdrawalCarrier431.validated_source_success','PublicRawAmountGuardAgreement.decoded_of_guarded_core_success','PublicCodecAgreement.parsePublic_of_decode'],'live_result':'toWire fixedProjection = some wire and SemanticPublicWire.parsePublic convertedOutput = some (SemanticPublicWire.toPublic wire)','parser_audit_target':'ExtractedRecordPayloadSoundness.parse_record_full_payload','mask_audit_target':'ExtractedMaskPreparedMul.current_prepared_correct','boundaries':['generated computation success is not a Rust/extractor/runtime correctness theorem','actual payment-helper success is explicit; verifier caller reachability/metadata not inferred','independently supplied caller public still needs binding to fixed projection','rows>=14 QM31 restriction, not M31 descent','selected-mask whole loop/sampler still open','J1.R16 syscall semantics remain release premises']}}
    rendered=json.dumps(data,indent=2)+'\n'
    if a.check:
        if OUT.read_text()!=rendered:raise ValueError('Manifest differs; regenerate deliberately')
        print('Verified',len(modules),'source modules,',len(order),'acyclic targets; no compiled object selected')
    else:
        OUT.write_text(rendered);print('Wrote',OUT.relative_to(ROOT),len(modules),'modules')
    if a.stage:
        destination=a.stage.resolve()
        if destination.exists():raise ValueError('Staging root must be new: '+str(destination))
        destination.mkdir(parents=True)
        for m in order:
            dest=destination/modules[m]['stage_as'];dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_bytes(source(modules[m]['source']))
        (destination/'SOURCE-MANIFEST.json').write_text(rendered)
        print('Staged',len(modules),'source files only at',destination)
if __name__=='__main__':main()
