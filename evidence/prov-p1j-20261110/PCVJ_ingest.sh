#!/bin/bash
# PCVJ_ingest.sh: receipts -> PCVJ_PROVED.json. A theorem is credited only if its scope exit is 0, its #print axioms line shows only
# propext/Classical.choice/Quot.sound, and it is one of the declared targets of the scope (CREDIT_TARGETS below).
cd "$(dirname "$0")"
python3 -B - <<'PY'
import json,re
STD={'propext','Classical.choice','Quot.sound'}
P='../prov-p2i-20261110/'
old=json.load(open(P+'PCUI_PROVED_OTHER.json'))
def axioms(a):
    r=json.load(open(f'PCVJ_{a}/receipt.json'));out={}
    for x in r['print_axioms']:
        x=re.sub(r'\s+',' ',x);m=re.match(r"'PRVEq\.([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",x)
        out[m.group(1)]={s.strip() for s in (m.group(2) or '').split(',') if s.strip()}
    return r,out
# (scope, file, tag, namespace, fresh_dir, emission run, config, targets)
T=[('L003','PRVEq_NHT_Constants_j1.lean','NHT_Constants_j1','NHT_Constants','prov-p1j-20261110/PCVJ_E001_emitted/raw/NHR_tx2_common','PCVJ_E001','ON',['compact.SPLIT']),
 ('L004','PRVEq_R1ExtractedM31Parser_j1.lean','R1ExtractedM31Parser_j1','AspisR1M31Parser','prov-p1j-20261110/PCVJ_E004_emitted/raw/NMH_field_decode','PCVJ_E004','ON',['field.M31.from_le_bytes']),
 ('L006','PRVEq_AspisR1RecordParser_Funs_j1.lean','AspisR1RecordParser.Funs_j1','AspisR1RecordParser','prov-p1j-20261110/PCVJ_E005_emitted/raw/NMH_wide_decode','PCVJ_E005','ON',['field.wide_exact.WideExact.BYTE_LEN','field.wide_exact.WideExact.from_limbs','field.wide_exact.WideExact.from_le_bytes']),
 ('L007','PRVEq_AdapterRwModel_j1.lean','AdapterRwModel_j1','AdapterRw',"prov-p1j-20261110/PCVJ_E007_emitted/raw/NMX_registry",'PCVJ_E007','ON',['r1_pool_adapter.AUDIT_POLICY_BINDING','r1_pool_adapter.VERIFIER_ENTRY_SEED','r1_pool_adapter.VERIFIER_ENTRY_V2_SEED','r1_pool_adapter.VERIFIER_REGISTRY_SEED','r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED']),
 ('L008','PRVEq_NMP_prepare_Funs_j1.lean','NMP_prepare.Funs_j1','NMP_prepare','prov-p1j-20261110/PCVJ_E003_emitted/raw/NJS_Extract','PCVJ_E003','ON',['verifier.Error.Insts.CoreConvertFromCodecError.from']),
 ('L010','PRVEq_NJS_Extract_Funs_j2.lean','NJS_Extract.Funs_j2','NJS_Extract','prov-p1j-20261110/PCVJ_E003_emitted/raw/NJS_Extract','PCVJ_E003','ON',['compact.FIXED','compact.MAGIC','compact.MAX_NODES','compact.MAX_PROOF','compact.OFF_NODES','compact.PROOF_BYTES','compact.QUERIES','transport.Variant.tag','verifier.candidate.batch_key_at']),
 ('L011','PRVEq_NMP_prepare_Funs_j3.lean','NMP_prepare.Funs_j3','NMP_prepare','prov-p1j-20261110/PCVJ_E008_emitted/raw/NMP_logical','PCVJ_E008','ON',['compact.LOGICAL_Y1']),
 ('L013','PRVEq_AspisR1TerminalDecoder_Funs_j1.lean','AspisR1TerminalDecoder.Funs_j1','AspisR1TerminalDecoder','prov-p1j-20261110/PCVJ_E009_emitted/raw/PCQG_aspis_statement_pair_terminal_b','PCVJ_E009','ON',['pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1','pool_v1.pair_terminal.validate_verified_afterstate','pool_v1.pair_terminal.validate_verified_afterstate_loop','pool_v1.pair_tree_profile.digest_is_canonical','pool_v1.pair_tree_profile.digest_is_canonical_loop','pool_v1.pair_tree_profile.digest_is_canonical_loop.body'])]
proved={}
# (a) the 10 theorems from the PCUI_ O1 bundle, re-proved in the clean file (scope PCVJ_L002 exit 0)
r,ax=axioms('L002');assert r['exit_status']==0
for d,v in old.items():
    nm=v['theorem'][len('PRVEq.'):]
    assert nm in ax and not (ax[nm]-STD),nm
    proved[d]=dict(theorem=v['theorem'],module=v['module'],receipt='prov-p1j-20261110/PCVJ_L002/receipt.json',proving_file='prov-p1j-20261110/PRVEq_O1clean.lean',config=v['config'],fresh_dir=v['fresh_dir'],kind='A_O1_CLEAN',supersedes_receipt=v['receipt'])
for sc,f,tag,ns,fd,run,cfg,targets in T:
    r,ax=axioms(sc);assert r['exit_status']==0,sc
    for t in targets:
        nm=tag+'.'+t;assert nm in ax,(sc,nm)
        assert not (ax[nm]-STD),(sc,nm,ax[nm])
        proved[ns+'.'+t]=dict(theorem='PRVEq.'+nm,module=tag.split('_j')[0],receipt=f'prov-p1j-20261110/PCVJ_{sc}/receipt.json',proving_file='prov-p1j-20261110/'+f,config=cfg,fresh_dir=fd,emission_run=run,kind='B_ON_EMISSION' if sc!='L013' else 'C_SECOND_SHAPE_TRANSPARENT_P')
json.dump(proved,open('PCVJ_PROVED.json','w'),indent=1)
import collections
print(len(proved),collections.Counter(v['kind'] for v in proved.values()))
PY
