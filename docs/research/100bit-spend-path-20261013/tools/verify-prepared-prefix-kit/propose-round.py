#!/usr/bin/env python3
"""Review-only one-round helper and explicit ten calls, with real arithmetic boundaries."""
from pathlib import Path
import argparse,difflib,hashlib,json,shutil,subprocess
sha=lambda b:hashlib.sha256(b).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--input',type=Path,required=True);a.add_argument('--out',type=Path,required=True);a.add_argument('--mask-boundary',action='store_true');a=a.parse_args()
old=(a.input/'fragments/verify_observed.rs').read_text();source=(a.input/'lib.rs').read_text();pins=json.loads((a.input/'source-pins.json').read_text())
start=old.index('    for round in 0..10 {');end=old.index('    mark(obs, 2);',start)
loop=old[start:end];body=loop.split(' {\n',1)[1][:-6];assert body.endswith('        running = value;\n')
bound='polynomial.iter().copied().fold(polynomial[0], QM31::add)'
value='''polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c))'''
assert body.count(bound)==1 and body.count(value)==1
boundary_helper='fn polynomial_boundary(polynomial:&[QM31;28])->QM31 {\n    '+bound+'\n}\n'
value_helper='fn polynomial_value(polynomial:&[QM31;28], alpha:QM31)->QM31 {\n    '+value.replace('alpha[round]','alpha')+'\n}\n'
roundbody=body.replace(bound,'polynomial_boundary(&polynomial)').replace(value,'polynomial_value(&polynomial, alpha)').replace('alpha[round] = transcript.semantic_validated','let alpha = transcript.semantic_validated')
config='''        #[cfg(feature = "prover")]
        {
            round_checks[round] = [running, boundary, value];
        }
        running = value;
'''
assert roundbody.count(config)==1
roundbody=roundbody.replace(config,'        Ok((alpha,boundary,value))\n')
round_helper='fn verify_round<H:Digest32>(prefix:&Prefix<\'_>, transcript:&mut SemanticTranscript<H>, round:usize, running:QM31)->Result<(QM31,QM31,QM31),Error> {\n'+roundbody+'}\n'
helpers=boundary_helper+'\n'+value_helper+'\n'+round_helper
calls=''.join('''    {
        let (a,boundary,value)=verify_round(&prefix,&mut transcript,ROUND,running)?;
        alpha[ROUND]=a;
        #[cfg(feature="prover")]
        {round_checks[ROUND]=[running,boundary,value];}
        running=value;
    }
'''.replace('ROUND',str(i)) for i in range(10))
new=old[:start]+calls+old[end:]
if a.mask_boundary:
 mstart=new.index('    let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(')
 mend=new.index('    let extra =',mstart)
 mask=new[mstart:mend];expr=mask[len('    let mask = '):].strip().removesuffix(';');expr=expr.replace('&alpha,','alpha,')
 helpers+='\nfn selected_mask(claims:&[[QM31;29];3], alpha:&[QM31;10])->QM31 {\n    '+expr+'\n}\n'
 new=new[:mstart]+'    let mask = selected_mask(&claims, &alpha);\n'+new[mend:]
 pins['opaque_paths'].append('crate::r1_semantic::selected_mask')
newlib=source.replace(old,helpers+'\n'+new,1)
a.out.mkdir(parents=True,exist_ok=True)
for p in a.input.rglob('*'):
 if p.is_file():
  d=a.out/p.relative_to(a.input);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
(a.out/'lib.rs').write_text(newlib);(a.out/'fragments/verify_observed.rs').write_text(new);(a.out/'fragments/verify_round.rs').write_text(round_helper);(a.out/'fragments/polynomial_helpers.rs').write_text(boundary_helper+'\n'+value_helper)
pins['classification']='PROPOSAL ONLY - not the accepted production source';pins['opaque_paths']+=['crate::r1_semantic::polynomial_boundary','crate::r1_semantic::polynomial_value']
pins['proposal']={'mode':'round-helper-mask' if a.mask_boundary else 'round-helper','actual_function_sha256':sha(old.encode()),'proposed_function_sha256':sha(new.encode()),'round_helper_sha256':sha(round_helper.encode()),'polynomial_helpers_sha256':sha((boundary_helper+'\n'+value_helper).encode()),'constraint':'Same row/first-error/call order; original two arithmetic folds moved verbatim to pure boundaries (alpha field alias only); loop body moved to checked one-round helper; ten sequential calls in index order, carry unchanged. No production source edit.'}
pins['kit_files']={str(p.relative_to(a.out)):sha(p.read_bytes()) for p in a.out.rglob('*') if p.is_file() and p.name not in ['source-pins.json','proposal.patch']}
(a.out/'source-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
root=Path(__file__).resolve().parents[5];file='crates/aspis-r1-cost-probe/src/r1_semantic.rs';fullold=subprocess.check_output(['git','-C',str(root),'show',pins['revision']+':'+file],text=True);assert fullold.count(old)==1
fullnew=fullold.replace(old,helpers+'\n'+new,1)
(a.out/'proposal.patch').write_text(''.join(difflib.unified_diff(fullold.splitlines(True),fullnew.splitlines(True),fromfile='a/'+file,tofile='b/'+file)))
print(json.dumps(pins['proposal']))
