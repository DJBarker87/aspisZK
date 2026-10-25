"""Focused offline source/package/import audit, no privileged/runtime validation."""
import ast
import json
from pathlib import Path
import subprocess
import types
from SbfSeal_setup import digest, require, PROBE, ROOT
from SbfSeal_admission import PRODUCER_PIN, SCOPE_ARGV

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
OUT=BASE/'evidence/sbf-seal-20261025'
ENTRY='50ab99cfbf3febcea66046e017be3e619ca8c732'


def main():
    checks=0
    def check(ok, why):
        nonlocal checks
        require(ok,why)
        checks+=1
    pins=json.loads((OUT/'SbfSeal-package-pins.json').read_bytes())
    for name,pin in pins['files'].items():
        check(digest((HERE/name).read_bytes())==pin,'package seal '+name)
    refs=json.loads((OUT/'SbfSeal-reference-pins.json').read_bytes())
    for row in refs:
        raw=subprocess.check_output(['git','show',row['revision']+':'+row['path']],cwd=BASE)
        check(digest(raw)=={k:row[k] for k in ('sha256','size')},'immutable reference '+row['path'])
    producer=next(r for r in refs if r['path'].endswith('ResourceRssGO_host.py'))
    check(PRODUCER_PIN=={k:producer[k] for k in ('sha256','size')},'actual producer source pin')
    future=json.loads((OUT/'SbfSeal-future-command.json').read_bytes())
    check(future['argv']==list(PROBE) and future['root']==ROOT,'literal future probe')
    check(future['approved_manifest_sha256']==[] and future['runtime_manifest'] is None,'disabled/runtime unknown')
    check(SCOPE_ARGV.count('MemoryMax=4G')==1 and SCOPE_ARGV.count('MemoryHigh=3G')==1 and
          SCOPE_ARGV.count('MemorySwapMax=0')==1 and SCOPE_ARGV.count('TasksMax=64')==1,'exact proposed scope')
    mapping=json.loads((OUT/'SbfSeal-input-map.json').read_bytes())
    check(len(mapping['packages'])==428,'current finite cache count')
    for row in mapping['packages']:
        check(row['archive']['sha256']==row['checksum'],'locked archive '+row['name'])
        check(row['selected_build_necessity'] is False,'not selected necessity')
    check(mapping['complete_per_file_mapping_available'] is False,'no invented runtime/source map')
    old=subprocess.check_output(['git','show',ENTRY+':tools/sbf-closure-20261025/SbfClosure_setup.py'],cwd=BASE).decode()
    calls={}
    for name,source in [('old',old),('new',(HERE/'SbfSeal_setup.py').read_text())]:
        tree=ast.parse(source)
        calls[name]=sorted({ast.unparse(n.func) for n in ast.walk(tree) if isinstance(n,ast.Call)})
    for name in ('SbfSeal_setup.py','SbfSeal_admission.py','SbfSeal_boundary.py'):
        tree=ast.parse((HERE/name).read_text())
        imports={n.names[0].name for n in ast.walk(tree) if isinstance(n,ast.Import)}
        check(not imports & {'ctypes','subprocess','socket','shutil'},'no syscall/shell backend '+name)
        for n in ast.walk(tree):
            if isinstance(n,ast.ExceptHandler):
                check(not any(isinstance(v,ast.Pass) for v in n.body),'no swallowed exception')
    changed=subprocess.check_output(['git','diff','--name-only',ENTRY],cwd=BASE,text=True).splitlines()
    check(all(p.startswith(('tools/sbf-seal-20261025/','evidence/sbf-seal-20261025/')) for p in changed),
          'assigned paths only')
    implementation=sum(len(p.read_text().splitlines()) for p in HERE.glob('*.py') if p.name!='SbfSeal_tests.py')
    check(implementation<=1200,'bounded implementation')
    detail=dict(checks=checks,implementation_lines=implementation,call_sets=calls,
                note='Full AST/text diff retained; source/import audit only. No kernel/backend/GO PASS.',
                authorized=False,print_axioms='N/A')
    (OUT/'SbfSeal-source-audit.json').write_text(json.dumps(detail,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(checks=checks,implementation_lines=implementation,authorized=False)))
    return types.SimpleNamespace(testsRun=checks,failures=[],errors=[],wasSuccessful=lambda:True)


if __name__=='__main__':main()
