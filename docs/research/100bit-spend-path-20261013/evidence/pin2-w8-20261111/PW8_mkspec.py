#!/usr/bin/env python3
"""PW8 (PIN2 W8): spec for the PIN2 emission of the verifier-prefix scope (r1_semantic::verify_observed with
r1_wire::Prefix::parse and r1_semantic::verify_finish opaque, plus semantic_validated, begin, public_transcript and
r0 Public::public_bytes). Derived from ../prov-p9f-20261110 PCXU_mkspec.py / PCXU_E003_spec.json: same tools
(Charon 454586e9 + Aeneas 0d21a9ec), same payload (git archive of c7593d23fdc), same env and features.
Changes: roots, the union of the PCXU_E003 and PCVL_E003 includes, two --opaque selectors, -abort-on-error added
to Aeneas (part of the PCVL_E003 recipe; changes nothing on success), workspace and namespace names.
usage: python3 PW8_mkspec.py RUN   (reads the committed PCXU_E003 spec via git show research:...)"""
import json,sys,subprocess
sys.dont_write_bytecode=True
run=sys.argv[1]
variant=sys.argv[2] if len(sys.argv)>2 else 'full'  # 'full' (E001) or 'noverify' (E002: verify_observed root and its two opaque boundaries removed after E001 failed in Aeneas: Arrow types)
d=json.loads(subprocess.check_output(['git','show','research:evidence/prov-p9f-20261110/PCXU_E003_spec.json']))
B='/home/dombarker/project-offloads/codex-pc-pin2-w8-20261111'
R0='aspis_statement::pool_v1::pair_forest_semantic_terminal::r0'
SFT=R0.rsplit('::',1)[0]
roots=['crate::r1_semantic::verify_observed','crate::r1_wire::_::semantic_validated','crate::r1_wire::begin','crate::r1_semantic::public_transcript',R0+'::_::public_bytes']
opaque_all=[('crate::r1_semantic::verify_finish','frozen model boundary: VerifyPrefix.Finish parameter F (fe80 binding-audit identifier_map)'),
        ('crate::r1_wire::_::parse','frozen model boundary: PrefixAdapter.parseAccepted (fe80 binding-audit identifier_map); only inherent parse in r1_wire is Prefix::parse (r1_wire.rs:292)')]
if variant=='noverify':
    roots=roots[1:];opaque=[]
elif variant=='noverify_types':
    # PW8_E004 (lead option A): E002 plus the verify_observed signature types that E002 does not reach, so that the whole
    # begin closure and Verified come from the PIN2 pair; verify_observed itself stays with PW8_E003.
    roots=roots[1:]+['crate::r1_semantic::Verified','aspis_core::circle::SecureCirclePoint'];opaque=[]
else:opaque=opaque_all
c=['cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for r in roots:c+=['--start-from',r]
for o,_ in opaque:c+=['--opaque',o]
inc=[R0,SFT+'::CompiledVariant',SFT+'::SemanticPublic',SFT+'::private_public',SFT+'::withdrawal_public','aspis_core::field::P','aspis_core::state_only_prefix::r0::Error',
 'crate::verifier::Prepared','crate::verifier::Accumulator','crate::verifier::BatchedWeights','crate::verifier::View','crate::verifier::Error','crate::verifier::Variant','crate::verifier::Phase','crate::verifier::QueryGeometry',
 'crate::r1_semantic::Verified','crate::r1_wire::SemanticTranscript','crate::r1_wire::Error','crate::r1_wire::Challenges',
 'aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint',
 'aspis_core::field::_::ZERO','aspis_core::field::_::new']
for t in inc:c+=['--include',t]
c+=['--dest-file',B+'/%s_emitted/repro.llbc'%run,'--','--manifest-path',B+'/PW8_workspace/crates/aspis-r1-cost-probe/Cargo.toml','--locked','--offline','--release','--lib','--jobs','4','--features','private-leaf-salts,optimized-terminal,program-build']
assert d['charon_command'][0]=='/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/charon'
d['charon_command']=[d['charon_command'][0]]+c
a=d['aeneas_command'];assert '-abort-on-error' not in a
a.insert(a.index('-backend'),'-abort-on-error')
a[a.index('-namespace')+1]='PW8_vp';a[a.index('-subdir')+1]='PW8_vp'
a[a.index('-dest')+1]=B+'/%s_emitted/raw'%run;a[-1]=B+'/%s_emitted/repro.llbc'%run
d['aeneas_command']=a
d['opacity']=[dict(path=o,why=w) for o,w in opaque]
d['configuration'].update(start_from=roots[:1],roots=roots,include=inc,opaque=[o for o,_ in opaque],namespace=['PW8_vp'])
d.update(run=run,spec_id=run,variant=variant,label='PIN2 W8 verifier-prefix scope at c7593d23fdc ('+('verify_observed; parse and verify_finish opaque' if variant=='full' else 'without verify_observed: semantic_validated, begin, public_transcript, public_bytes')+')',derived_from='prov-p9f-20261110/PCXU_E003_spec.json')
d['supersedes']={'earlier_run':'none (first PIN2 emission of verify_observed); frozen counterparts: fe80 verify-helper-prefix emission and PCVL_E003','change':'source c7593d23fdc, second tool version, real crate instead of mirror crate'}
d['covers']={}
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run)
# ---- variant 'fe80' (PW8_E003, approved by the lead after PW8_E001 failed in Aeneas 0d21a9ec on the arrow type):
# exactly the fe80 verify-helper-prefix configuration on the real crate at c7593d23fdc: Charon daad69be (XRa_bin) +
# Aeneas b59d5188-lean432-extended, root verify_observed, opaque parse/public_transcript/begin/verify_finish
# (tools/verify-helper-prefix-kit/prepare.py record), includes = the PCVL_E003 type includes (no statement-crate fn includes,
# which the old Aeneas cannot translate: PCVL_E002/E004). Features: the PIN2 program set (the crate has no r0 feature;
# fe80's r0,private-leaf-salts applied to the mirror crate); detail-phases off in both.
if variant=='fe80':
    X='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
    c=['cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from','crate::r1_semantic::verify_observed']
    op=[('crate::r1_wire::_::parse','fe80 opaque_paths; binds to PrefixAdapter.parseAccepted'),('crate::r1_semantic::public_transcript','fe80 opaque_paths; binds by name to PIN2_NEWGATE_r1_semantic'),('crate::r1_wire::begin','fe80 opaque_paths; binds by name to the PW8_E002 emission'),('crate::r1_semantic::verify_finish','fe80 opaque_paths; parameter F')]
    for o,_ in op:c+=['--opaque',o]
    inc=['crate::verifier::Prepared','crate::verifier::Accumulator','crate::verifier::BatchedWeights','crate::verifier::View','crate::verifier::Error','crate::verifier::Variant','crate::verifier::Phase','crate::verifier::QueryGeometry','crate::r1_semantic::Verified','crate::r1_wire::SemanticTranscript','crate::r1_wire::Challenges','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint']
    for t in inc:c+=['--include',t]
    c+=['--dest-file',B+'/%s_emitted/repro.llbc'%run,'--','--manifest-path',B+'/PW8_workspace/crates/aspis-r1-cost-probe/Cargo.toml','--locked','--offline','--release','--lib','--jobs','4','--features','private-leaf-salts,optimized-terminal,program-build']
    d['charon_command']=[X+'/charon']+c
    d['aeneas_command']=[X+'/aeneas-b59d5188-extended','-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PW8_vo','-dest',B+'/%s_emitted/raw'%run,'-subdir','PW8_vo','-split-files',B+'/%s_emitted/repro.llbc'%run]
    d['opacity']=[dict(path=o,why=w) for o,w in op]
    d['configuration'].update(start_from=['crate::r1_semantic::verify_observed'],roots=['crate::r1_semantic::verify_observed'],include=inc,opaque=[o for o,_ in op],namespace=['PW8_vo'])
    d.update(aeneas_tool='extended',aeneas_sha256='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958',charon_sha256='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',
             tool_label='ORIGINAL/fe80 TOOL (Charon daad69be XRa_bin / Aeneas b59d5188-lean432-extended)',label='PIN2 W8 verify_observed at c7593d23fdc, fe80 configuration')
    d.pop('charon_driver_sha256',None)
    json.dump(d,open(run+'_spec.json','w'),indent=1);print(run,'fe80')
