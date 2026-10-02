#!/usr/bin/env python3
"""Read-only portable integrity/status verifier for the R425 diagnostic bundle."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((ROOT/'bundle-manifest.json').read_text())
missing=[];bad=[]
for rel,want in manifest['files'].items():
 p=ROOT/rel
 if not p.is_file():missing.append(rel)
 elif sha(p)!=want:bad.append({'path':rel,'expected':want,'actual':sha(p)})
for p in ROOT.rglob('*'):
 if p.is_file() and p.suffix.lower() in {'.exe','.cmo','.cmx','.o','.a','.so','.pyc'}: bad.append({'path':str(p.relative_to(ROOT)),'error':'compiled/cache artifact unexpectedly included'})
main=json.loads((ROOT/'build-preflight/r425-main-build-v1/result.json').read_text())
main_cmd=json.loads((ROOT/'build-preflight/r425-main-build-v1/command.json').read_text())
translation=json.loads((ROOT/'translation-runner/output/ee7ba72da456-20261002T210856Z/result.json').read_text())
translation_log=(ROOT/'translation-runner/output/ee7ba72da456-20261002T210856Z/translate.log').read_text(errors='replace')
fixture11=json.loads((ROOT/'build-preflight/r425-unit-fixture-execution-v1/result.json').read_text())
fixture8=json.loads((ROOT/'build-preflight/r425-unit-evaluator-execution-v1/result.json').read_text())
saved_audit=json.loads((ROOT/'saved-translation-audit/audit.json').read_text())
checks={
 'saved_main_translation_audit_pass':saved_audit['result']=='PASS',
 'main_build_exit_zero':main['exit_status']==0,
 'main_and_translation_binary_hash_match':main['binary_sha256']==translation['binary_sha256'],
 '11_check_fixture_passed':fixture11['all_checks_passed'] is True and fixture11['assertions_passed']==11,
 '8_check_fixture_passed':fixture8['all_checks_passed'] is True and fixture8['assertions_passed']==8,
 'translation_exit_two':translation['translator_exit_status']==2,
 'translation_emitted_no_lean':translation['translation_result']['generated_dir_exists'] is False and translation['translation_result']['translation_json_exists'] is False and translation['translation_result']['manifest_function_entries']==0,
 'translation_mutable_borrow_error':"Can't copy a mutable borrow" in translation_log and 'iterator.rs' in translation_log and 'InterpExpressions.ml, line 234' in translation_log,
 'translation_axioms_na':translation['scope']=='Translation inventory only; no Lean compile, template fill, proof, or source claim.' and not list(ROOT.rglob('*.olean')),
}
report={'result':'PASS' if not missing and not bad and all(checks.values()) else 'FAIL','bundle_file_count':len(manifest['files']),'missing_files':missing,'hash_or_exclusion_errors':bad,'checks':checks,'scope':'Read-only saved-evidence verification; no build, fixture, translation, or Lean job.'}
print(json.dumps(report,indent=2))
sys.exit(0 if report['result']=='PASS' else 1)
