#!/usr/bin/env python3
"""Scoped frontend regression, not a Rust-library admission theorem.

Positive optimized MIR must emit exactly the successful built-MIR Lean.
Synthetic negative LLBC inputs must leave the unsupported copy in place and
the strict interpreter must reject it. Run inside the capped receipt runner.
"""
import argparse, copy, hashlib, importlib.util, json, os, re, subprocess, time
from pathlib import Path

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--revision',required=True)
    args=ap.parse_args(); root=args.root; out=args.out
    out.mkdir(parents=True,exist_ok=False)
    script=root/'normalize-deref-temporaries.py'
    spec=importlib.util.spec_from_file_location('normalizer',script)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    raw=root/'CuDerefReproOptimized.llbc'
    original=module.decode_hashcons(json.loads(raw.read_bytes()),{})
    _,positive=module.normalize(copy.deepcopy(original))
    assert len(positive['changes'])==2 and not positive['rejected']
    site=next(x for x in positive['changes'] if x['function']==0)
    def block_of(doc):
        body=doc['translated']['fun_decls'][0]['body']['Structured']
        block=body['body']
        for part in site['block']:block=block[part]
        return body,block['statements']
    cases={}
    cases['positive']=copy.deepcopy(original)
    extra=copy.deepcopy(original);body,statements=block_of(extra)
    j=next(i for i,s in enumerate(statements) if s['id']==site['borrow_statement'])
    statements.insert(j+1,copy.deepcopy(statements[j]));cases['extra-use']=extra
    named=copy.deepcopy(original);body,_=block_of(named)
    body['locals']['locals'][site['temporary']]['name']='retained_snapshot'
    cases['named-local']=named
    interrupted=copy.deepcopy(original);body,statements=block_of(interrupted)
    i=next(i for i,s in enumerate(statements) if s['id']==site['copy_statement'])
    source=copy.deepcopy(site['source_place'])
    write=copy.deepcopy(statements[i]);write['kind']={'Assign':[source,{'Use':[{'Move':copy.deepcopy(source)},'No']}]}
    statements.insert(i+1,write);cases['intervening-write']=interrupted
    storage=copy.deepcopy(original);body,statements=block_of(storage)
    i=next(i for i,s in enumerate(statements) if s['id']==site['copy_statement'])
    marker=copy.deepcopy(statements[i]);marker['kind']={'StorageDead':min(module.local_ids(site['source_place']))}
    statements.insert(i+1,marker);cases['source-storage-dead']=storage
    records=[]
    for name,doc in cases.items():
        case=out/name;case.mkdir()
        # Renumber synthetic statement IDs; negative inputs are deliberately
        # not claimed to have come from Rust or to be borrow-checker valid.
        if name!='positive':
            for function in doc['translated']['fun_decls']:
                if function is None or not isinstance(function.get('body'),dict):continue
                structured=function['body'].get('Structured')
                if structured:
                    n=0
                    for _,block in module.blocks(structured['body']):
                        for statement in block['statements']:statement['id']=n;n+=1
        normalized,report=module.normalize(doc)
        changed={x['function'] for x in report['changes']}
        assert changed==({0,1} if name=='positive' else {1}), (name,report)
        if name!='positive':assert any(x['function']==0 for x in report['rejected'])
        source=case/'input.llbc';source.write_text(json.dumps(doc,separators=(',',':'))+'\n')
        target=case/'normalized.llbc';target.write_text(json.dumps(normalized,separators=(',',':'))+'\n')
        (case/'normalization.json').write_text(json.dumps(report,indent=2)+'\n')
        generated=case/'generated'
        command=[str(root/'aeneas-no-branch-join/bin/aeneas'),'-checks','-no-progress-bar','-sequential',
            '-backend','lean','-namespace','AspisR1CuDeref','-dest',str(generated),
            '-subdir','AspisR1CuDeref','-split-files','-emit-json',str(target)]
        started=time.monotonic()
        with (case/'stdout.log').open('w') as stdout,(case/'stderr.log').open('w') as stderr:
            result=subprocess.run(['/usr/bin/time','-v','-o',str(case/'time.log'),*command],
                cwd=root/'deref-repro-input',env=dict(os.environ,AENEAS_DISABLE_BRANCH_JOIN='1'),
                stdout=stdout,stderr=stderr,timeout=90)
        timing=(case/'time.log').read_text()
        def metric(label):return int(re.search(re.escape(label)+r':\s*(\d+)',timing)[1])
        combined=(case/'stdout.log').read_text()+(case/'stderr.log').read_text()
        if name=='positive':
            assert result.returncode==0,combined
            for file in ['Types.lean','Funs.lean']:
                assert (generated/'AspisR1CuDeref'/file).read_bytes()==(root/'generated-deref-repro-a/AspisR1CuDeref'/file).read_bytes()
        else:
            assert result.returncode!=0 and "Can't copy a mutable borrow" in combined,(name,result.returncode,combined)
        record=dict(case=name,synthetic_negative=name!='positive',command=command,
            source_revision=args.revision,features=[],exit_status=result.returncode,
            wall_seconds=time.monotonic()-started,peak_rss_kib=metric('Maximum resident set size (kbytes)'),
            process_swaps=metric('Swaps'),print_axioms='N/A: frontend diagnostic, no Lean run',
            input_sha256=sha(source),normalized_sha256=sha(target),normalizer_sha256=sha(script),
            changed_functions=sorted(changed),rejections=report['rejected'],
            generated_lean={p.name:sha(p) for p in (generated/'AspisR1CuDeref').glob('*.lean')})
        (case/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');records.append(record)
    summary=dict(status='PASS_FRONTEND_REGRESSION_NOT_LIBRARY_ADMISSION',cases=records,
        original_input_sha256=sha(raw),harness_sha256=sha(Path(__file__)),normalizer_sha256=sha(script),
        positive_matches_built_mir_byte_for_byte=True,negative_copies_remain_rejected=True)
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(dict(status=summary['status'],cases=len(records))))

if __name__=='__main__':main()
