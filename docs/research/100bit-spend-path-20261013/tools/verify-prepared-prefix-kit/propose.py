#!/usr/bin/env python3
"""Create review-only alternatives, never modify the production candidate."""
from pathlib import Path
import argparse,difflib,hashlib,json,shutil
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--mode',choices=['while','straight','straight-closure','prepared-owned','prepared-helper','prepared-helper-fields'],required=True);a=ap.parse_args()
 source=(a.input/'lib.rs').read_text();fragment='prepared_new.rs' if a.mode in ['prepared-owned','prepared-helper','prepared-helper-fields'] else 'verify_observed.rs';old=(a.input/'fragments'/fragment).read_text();assert source.count(old)==1
 if a.mode in ['prepared-owned','prepared-helper','prepared-helper-fields']:
  start=old.index('        let mut alpha=[t.scalar(29,v.round0,false),E::ZERO];')
  end=old.index('        let queries=t.queries(row,v.final_message)?;',start)
  replacement="""        let alpha0=t.scalar(29,v.round0,false);
        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
"""
 else:
  start=old.index('    for round in 0..10 {');end=old.index('    mark(obs, 2);',start)
  loop=old[start:end];assert loop.endswith('    }\n');body=loop.split(' {\n',1)[1][:-6];assert body.endswith('        running = value;\n')
  if a.mode=='while':
   replacement='    let mut round = 0usize;\n    while round < 10 {\n'+body+'        round += 1;\n    }\n'
  else:
   replacement=''.join('    {\n        let round = '+str(i)+'usize;\n'+body+'    }\n' for i in range(10))
 new=old[:start]+replacement+old[end:]
 if a.mode=='straight-closure':
  assert new.count('.fold(polynomial[0], QM31::add)')==10
  new=new.replace('.fold(polynomial[0], QM31::add)','.fold(polynomial[0], |a, c| a.add(c))')
 helper='';moved=''
 if a.mode in ['prepared-helper','prepared-helper-fields']:
  tstart=new.index('        let g=powers::<29>(gamma);let k=powers::<7>(kappa);')
  tend=new.index('        Ok(Box::new(Self{',tstart)
  moved=new[tstart:tend]
  if a.mode=='prepared-helper-fields':
   assert moved.count('v.inactive')==1 and moved.count('v.y1')==1
   moved=moved.replace('v.inactive','inactive').replace('v.y1','y1')
  helper='fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<\'_>,gamma:E,kappa:E)->Result<E,Error> {\n'+moved+'        Ok(claim)\n}\n'
  if a.mode=='prepared-helper-fields':helper=helper.replace("v:&View<'_>",'y1:&[u8],inactive:E')
  new=new[:tstart]+'        let claim=prepared_claim(sem,v,gamma,kappa)?;\n'+new[tend:]
 if a.mode=='prepared-helper-fields':new=new.replace('prepared_claim(sem,v,gamma,kappa)','prepared_claim(sem,v.y1,v.inactive,gamma,kappa)')
 newlib=source.replace(old,new,1)
 if helper:
  assert newlib.count(' impl Prepared {')==1
  newlib=newlib.replace(' impl Prepared {',helper+'\n impl Prepared {',1)

 if not helper:assert source[:source.index(old)]==newlib[:newlib.index(new)]
 a.out.mkdir(parents=True,exist_ok=True)
 for p in a.input.rglob('*'):
  if p.is_file():
   d=a.out/p.relative_to(a.input);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
 (a.out/'lib.rs').write_text(newlib);(a.out/'fragments'/fragment).write_text(new)
 if helper:(a.out/'fragments/prepared_claim.rs').write_text(helper)
 pins=json.loads((a.input/'source-pins.json').read_text());pins['classification']='PROPOSAL ONLY - not the accepted production source';
 if helper:pins['opaque_paths'].append('crate::verifier::prepared_claim')
 pins['proposal']={'mode':a.mode,'base_lib_sha256':sha(source.encode()),'fragment':fragment,'actual_function_sha256':sha(old.encode()),'proposed_function_sha256':sha(new.encode()),'constraint':(('Owned(alpha,row) branch; entire arithmetic tail moved into Result-returning helper called after rho; exact bytes modulo v.inactive/inactive and v.y1/y1 aliases when field parameters selected; same transcript/error order; proposal only.' if helper else 'Owned(alpha,row) folds-branch; same transcript/error order; proposal only.') if a.mode in ['prepared-owned','prepared-helper','prepared-helper-fields'] else 'Only loop-control form changed. Same body, checked reads, arithmetic, row order, failure paths and running=value update; no production file edited.')}
 pins['kit_files']={str(p.relative_to(a.out)):sha(p.read_bytes()) for p in a.out.rglob('*') if p.is_file() and p.name not in ['source-pins.json','proposal.patch']}
 (a.out/'source-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
 file='verifier.rs' if a.mode in ['prepared-owned','prepared-helper','prepared-helper-fields'] else 'r1_semantic.rs'
 import subprocess
 fullold=subprocess.check_output(['git','-C',str(Path(__file__).resolve().parents[5]),'show',pins['revision']+':crates/aspis-r1-cost-probe/src/'+file],text=True)
 assert fullold.count(old)==1
 fullnew=fullold.replace(old,new,1)
 if helper:fullnew=fullnew.replace('impl Prepared {',helper+'\nimpl Prepared {',1)
 patch=''.join(difflib.unified_diff(fullold.splitlines(True),fullnew.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/'+file,tofile='b/crates/aspis-r1-cost-probe/src/'+file))
 if moved:
  pins['proposal']['moved_tail_sha256']=sha(moved.encode());pins['proposal']['helper_sha256']=sha(helper.encode());pins['proposal']['new_boundary']='crate::verifier::prepared_claim';pins['proposal']['helper_statement']=helper.split('{',1)[0]
  (a.out/'source-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
 (a.out/'proposal.patch').write_text(patch)
 print(json.dumps(pins['proposal']))
if __name__=='__main__':main()
