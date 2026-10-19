#!/usr/bin/env python3
"""Isolate one unchanged normalized library loop for strict frontend diagnosis.

All other function bodies become opaque; their signatures and every type/trait
are retained. This is a diagnostic projection, never source-library admission.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess

def sha(data):return hashlib.sha256(data).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--borrow-check',action='store_true');args=ap.parse_args()
    raw=(args.root/'CuArrayDerefNormalized.llbc').read_bytes()
    normalized=json.loads((args.root/'runs/array-deref-normalize-a/normalization.json').read_bytes())
    assert sha(raw)==normalized['output_sha256']
    doc=json.loads(raw);functions=doc['translated']['fun_decls']
    selected=functions[40]
    assert selected['def_id']==40 and selected['item_meta']['span']['data']['beg']['line']==906
    body=json.dumps(selected,sort_keys=True)
    removed=[]
    for function in functions:
        if function is not None and function['def_id']!=40 and function['body']!='Opaque':
            function['body']='Opaque';removed.append(function['def_id'])
    assert json.dumps(functions[40],sort_keys=True)==body
    args.out.mkdir(parents=True,exist_ok=False)
    encoded=(json.dumps(doc,separators=(',',':'))+'\n').encode()
    target=args.out/'CuArrayLoopOnly.llbc';target.write_bytes(encoded)
    (args.out/'projection.json').write_text(json.dumps(dict(status='DIAGNOSTIC_ONLY',
        input_sha256=sha(raw),output_sha256=sha(encoded),selected_function=40,
        selected_function_sha256=sha(body.encode()),opaque_body_ids=removed,
        selected_body_unchanged=True,all_signatures_types_traits_unchanged=True),indent=2)+'\n')
    command=[str(args.root/'aeneas-no-branch-join/bin/aeneas'),'-checks','-abort-on-error',
        '-log','InterpLoopsFixedPoint,InterpMatchCtxs','-no-progress-bar','-sequential',
        '-backend','lean','-namespace','AspisR1CuArrayLoopOnly','-dest',str(args.out/'generated'),
        '-subdir','AspisR1CuArrayLoopOnly','-split-files',str(target)]
    if args.borrow_check:
        command=command[:3]+['-borrow-check','-log','InterpLoopsFixedPoint,InterpMatchCtxs',
            '-no-progress-bar','-sequential',str(target)]
    (args.out/'command.json').write_text(json.dumps(command,indent=2)+'\n')
    raise SystemExit(subprocess.run(command,cwd=args.root/'cu-dots-input').returncode)

if __name__=='__main__':main()
