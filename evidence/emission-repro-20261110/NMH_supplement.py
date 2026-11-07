#!/usr/bin/env python3
"""Plan bounded source-annotation probes where original configuration is absent.
These probes test native definitions; they never claim to recover a missing
reference driver or silently assign a guessed historical configuration.
"""
from pathlib import Path
import json,subprocess,re,copy
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/codex-cx-emission-repro-20261110'
def main():
 plan=json.loads((E/'NMH_PLAN.json').read_text());inv=json.loads((E/'NMH_INVENTORY.json').read_text())['blobs']
 probes=[
 ('compact-view',['crate::compact::compact_row'],['crate::verifier::echeck']),
 ('field-decode',['aspis_core::field::_::from_le_bytes'],[]),
 ('wide-decode',['aspis_core::field::wide_exact::_::from_le_bytes'],[]),
 ('checkpoint-validate',['crate::verifier::validate_checkpoint_queries'],[]),
 ('checkpoint-weights',['crate::verifier::read_checkpoint_weights'],['aspis_core::r0::heap::filled']),
 ('checkpoint-size',['crate::verifier::checkpoint_size'],[]),
 ('wide-serialize',['aspis_core::field::wide_exact::_::to_le_bytes'],[]),
 ('fast-dots',['crate::fast_dots::four_dots_one'],['aspis_core::field::_::mul','aspis_core::field::wide_exact::_::mul']),
 ('weight-finish',['crate::verifier::_::finish'],['aspis_core::field::wide_exact::_::mul','aspis_core::field::wide_exact::_::add','crate::fast_dots::four_dots']),
 ('sampler',['crate::sampler::ordinary_sample'],[]),
 ('transcript-sample',['aspis_core::transcript::_::challenge_qm31'],[]),
 ('compact-expand',['crate::compact::expand_semantic'],['crate::compact::check_values']),
 ('field-inv-core',['aspis_core::field::_::inv'],[]),
 ('residue-update',['crate::verifier::update_residue_row'],['aspis_core::field::_::mul','aspis_core::field::wide_exact::_::mul']),
 ('weight-push',['crate::weights::push_byte_products'],['aspis_core::field::_::mul','aspis_core::field::wide_exact::_::mul']),
 ('compact-values',['crate::compact::check_values'],[]),
 ('terminal-validation',['aspis_statement::pool_v1::pair_forest_terminal::validate_pool_v1_pair_forest_terminal_statement_v1'],[]),
 ('canonical-scan',['crate::verifier::candidate::canonical_scan'],[]),
 ('wire-record',['crate::r1_wire::parse_record'],[]) ]
 template=json.loads((E/'NMH_E001.json').read_text());base=plan['runs'][0]['configuration']
 for i,(label,roots,opaque) in enumerate(probes,12):
  run='NMH_E%03d'%i;out=H+'/'+run+'_emitted';llbc=out+'/repro.llbc'
  # Map to explicitly named annotations; retain all plausible blob aliases.
  matches=[]
  for z in inv:
   for a in z['annotations']:
    if any(a['name'].split('::')[-1]==r.split('::')[-1] for r in roots):matches.append(z['blob']);break
  assert matches,(label,'no corpus member')
  cc=[base['charon_command'][0],'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
  for r in roots:cc+=['--start-from',r]
  for r in opaque:cc+=['--opaque',r]
  cc+=['--dest-file',llbc,'--','--manifest-path',H+'/NMH_workspace/crates/aspis-r1-cost-probe/Cargo.toml','--locked','--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
  ns='NMH_'+label.replace('-','_');ac=[base['aeneas_command'][0],'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',out+'/raw','-subdir',ns,'-split-files',llbc]
  c=dict(charon_command=cc,aeneas_command=ac,roots=roots,opaque=opaque,manifest='crates/aspis-r1-cost-probe/Cargo.toml',namespace=[ns],receipt=None)
  # No credit from invented opacity: documented as a diagnostic split, not original config.
  r=dict(run=run,label=label,configuration=c,charon_command=cc,aeneas_command=ac,opacity=[],groups=[g['group'] for g in plan['groups'] if set(matches)&set(g['members'])],members=sorted(set(matches)),bytes=sum(z['bytes'] for z in inv if z['blob'] in matches),basis='Diagnostic native-definition projection from archived source annotation; original historical full configuration remains unresolved. Deployed verifier features and NHR core Option/Result includes. Opaque boundaries are explicit in command, not a fidelity claim.',diagnostic_only=True)
  (E/(run+'_spec.json')).write_text(json.dumps(r,indent=2)+'\n');cfg=copy.deepcopy(template);cfg.update(attempt=run,module=label,command=['python3','NMH_extract.py',run],collect=[run+'_emitted','NMH_TOOL_ATTEMPTS.jsonl']);cfg['upload']=[n if n!='NMH_E001_spec.json' else run+'_spec.json' for n in cfg['upload']];cfg['sources']=[n if n!='NMH_E001_spec.json' else run+'_spec.json' for n in cfg['sources']];(E/(run+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');plan['runs'].append(r)
 (E/'NMH_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');print('planned',len(plan['runs']),'serial extraction attempts')
if __name__=='__main__':main()
