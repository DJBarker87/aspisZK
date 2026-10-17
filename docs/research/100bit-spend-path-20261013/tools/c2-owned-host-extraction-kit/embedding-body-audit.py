#!/usr/bin/env python3
"""Raw current Lean bodies/signatures plus explicit prior-carrier naming audit."""
from pathlib import Path
import argparse,difflib,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 spec=importlib.util.spec_from_file_location('inventory',BASE/'tools/j1-integrated-declaration-repin.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 gen=BASE/'lean/c2-host-embedding-20261017/AspisC2HostEmbedding';prior=BASE/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation';current={};old={}
 for n in ['Types.lean','Funs.lean']:
  current.update(m.lean_declarations((gen/n).read_bytes()));old.update(m.lean_declarations((prior/n).read_bytes()))
 mappings={'aspis_core.field.WideExact':'field.wide_exact.WideExact','aspis_core.field.M31':'field.M31','aspis_core.field.CM31':'field.CM31','aspis_core.field.QM31':'field.QM31','aspis_core.field.P':'field.P'}
 def rename(s):
  for x,y in sorted(mappings.items(),key=lambda p:-len(p[0])):s=s.replace(x,y)
  return s
 checks=[]
 for oldname,newname in [('aspis_core.field.M31','field.M31'),('aspis_core.field.CM31','field.CM31'),('aspis_core.field.QM31','field.QM31'),('aspis_core.field.WideExact','field.wide_exact.WideExact'),('aspis_core.field.P','field.P'),('aspis_core.field.QM31.ZERO','field.QM31.ZERO')]:
  assert oldname in old and newname in current
  renamed=[rename(t) for t in old[oldname]['tokens']];assert renamed==current[newname]['tokens'],(oldname,newname)
  checks.append({'previous':oldname,'current':newname,'previous_body_sha256':old[oldname]['body_sha256'],'renamed_body_sha256':sha(m.canonical(renamed)),'current_body_sha256':current[newname]['body_sha256'],'classification':'exact token equality after explicit identifier mapping; distinct Lean namespaces are not silently identified'})
 decls=[]
 for n,x in current.items():
  item={k:x[k] for k in ['body_sha256','signature','signature_sha256']};item['declaration']=n;item['full_name']='AspisC2HostEmbedding.'+n
  previous=next((c for c in checks if c['current']==n),None)
  item['classification']='retained carrier/global body after explicit naming expansion' if previous else 'new emitted body/closure or synthetic root; no preceding accepted body to diff'
  item['prior_accepted_body']=previous['previous'] if previous else None
  decls.append(item)
 boundary='fromQm : aspis_core.field.QM31 → Result aspis_core.field.WideExact'
 new=current['field.wide_exact.WideExact.from_qm31']['signature']
 report={'generated_files':{n:sha((gen/n).read_bytes()) for n in ['Types.lean','Funs.lean']},'declarations':decls,'declaration_count':len(decls),'prior_carrier_file_hashes':{n:sha((prior/n).read_bytes()) for n in ['Types.lean','Funs.lean']},'explicit_identifier_mapping':mappings,'six_prior_declaration_checks':checks,'from_qm31_prior_boundary_statement':boundary,'from_qm31_current_statement':new,'from_qm31_statement_diff':''.join(difflib.unified_diff((boundary+'\n').splitlines(True),(new+'\n').splitlines(True),fromfile='prior universal boundary field (not a generated body)',tofile='fresh actual body in new namespace')),'scope':'Raw generated files unchanged, no external template/axiom import. This fresh extraction does not automatically bind the prior Prepared/tx1 B.fromQm: nominal transport remains a separate explicit obligation. Actual Backend/build/encoder ownership is not claimed.'}
 b=(json.dumps(report,indent=2,sort_keys=True)+'\n').encode()
 if a.check:assert a.out.read_bytes()==b
 else:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(b)
 print(json.dumps({'check':a.check,'declarations':len(decls),'retained_named_carriers_globals':len(checks),'audit_sha256':sha(b)}))
if __name__=='__main__':main()
