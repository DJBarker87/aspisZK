#!/usr/bin/env python3
"""PCXU: spec for the PIN2 emission of r1_semantic::public_transcript. Derived from PCXQ_E001_spec.json (same tools/env), root and includes changed.
usage: python3 PCXU_mkspec.py RUN"""
import json,sys
sys.dont_write_bytecode=True
run=sys.argv[1]
d=json.load(open('../prov-p9a-20261110/PCXQ_E001_spec.json'))
B='/home/dombarker/project-offloads/codex-pc-prov-p9a-20261110'
R0='aspis_statement::pool_v1::pair_forest_semantic_terminal::r0'
inc=['core::option::Option','core::result::Result','core::option::_::ok_or','--start-from',
 'crate::r1_semantic::public_transcript']
c=['cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or',
 '--start-from','crate::r1_semantic::public_transcript']
for x in ['--start-from',R0+'::_::public_bytes']: c.append(x)
for t in [R0,R0.rsplit('::',1)[0]+'::CompiledVariant',R0.rsplit('::',1)[0]+'::SemanticPublic',R0.rsplit('::',1)[0]+'::private_public',R0.rsplit('::',1)[0]+'::withdrawal_public','aspis_core::field::P','aspis_core::state_only_prefix::r0::Error','crate::r1_wire::SemanticTranscript','crate::r1_wire::Error','crate::r1_wire::Challenges',
 'aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint']:
    c+=['--include',t]
c+=['--dest-file',B+'/%s_emitted/repro.llbc'%run,'--','--manifest-path',B+'/PCXU_workspace/crates/aspis-r1-cost-probe/Cargo.toml','--locked','--offline','--release','--lib','--jobs','4','--features','private-leaf-salts,optimized-terminal,program-build']
d['charon_command']=['/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/charon']+c
a=d['aeneas_command'];a[a.index('-namespace')+1]='PCXU_r1sem';a[a.index('-subdir')+1]='PCXU_r1sem'
a[a.index('-dest')+1]=B+'/%s_emitted/raw'%run;a[-1]=B+'/%s_emitted/repro.llbc'%run
d['aeneas_command']=a
d['configuration'].update(start_from=['crate::r1_semantic::public_transcript'],roots=['crate::r1_semantic::public_transcript',R0+'::_::public_bytes'],namespace=['PCXU_r1sem'],features='private-leaf-salts,optimized-terminal,program-build',manifest='crates/aspis-r1-cost-probe/Cargo.toml',crate='aspis-r1-cost-probe')
d.update(run=run,spec_id=run,label='PIN2 r1_semantic::public_transcript at c7593d23fdc (with r0 public_bytes closure)',frozen_revision='c7593d23fdc56fcee9a9df1628d5f63b52ac7a95',frozen_source_tree_git_hash='41502cde12546a508272e75d71f0e5a9e449780e',derived_from='prov-p9a-20261110/PCXQ_E001_spec.json')
d['supersedes']={'earlier_run':'PCVJ_E006 (4bb3b3f, public_bytes external)','change':'source revision, public_bytes extracted not external'}
d['covers']={}
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run)
