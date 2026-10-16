#!/usr/bin/env python3
"""Check exact emitted first body after explicit boundary/type parameterization."""
from pathlib import Path
import argparse,hashlib,json,re
R=Path(__file__).resolve().parents[5]
B=R/'docs/research/100bit-spend-path-20261013'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--generated',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 raw=(a.generated/'AspisR1FirstDiagnostic/Funs.lean').read_text();source=B/'lean/ExtractedFirstCallerReachability.lean';new=source.read_text()
 oldfirst=raw[raw.index('def first\n'):raw.rindex('\nend AspisR1FirstDiagnostic')].strip()
 newfirst=new[new.index('def first {'):new.index('\nprivate theorem bind_success')].strip()
 oldsig,oldbody=oldfirst.split(':= do',1);newsig,newbody=newfirst.split(':= do',1)
 # The body keeps every bind, match, callback, observer argument and error map.
 replacements=[('decode_pool_v1_pair_forest_terminal_statement_v1','decode'),
 ('first.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorProgramError','(decodeErrorClosure invalidAccountData)'),
 ('verifier.tx1','tx1'),('verifier.Error','F'),('ProgramError','E'),('Std.U8','U8')]
 transformed=oldbody
 for old,n in replacements:
  assert old in transformed,old;transformed=transformed.replace(old,n)
 compact=lambda s:re.sub(r'\s+','',s)
 transformed=compact(transformed).replace('some(mark)','somemark').replace('(error)','error')
 assert transformed==compact(newbody),'complete first body changed beyond the documented boundary binding'
 # Exact generated selector body has already been checked in the preparation
 # model; this comparison prevents silently choosing a different projection.
 selector=raw[raw.index('def\n  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public'):raw.index('/-- [aspis_r1_first_diagnostic::first::{impl')]
 prep=(B/'lean/extracted-public-preparation-20261016/AspisR1PublicPreparation/Funs.lean').read_text()
 marker='def\n  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public'
 start=prep.index(marker);end=prep.index('/--',start)
 assert compact(selector)==compact(prep[start:end])
 external=(a.generated/'AspisR1FirstDiagnostic/FunsExternal_Template.lean').read_text()
 assert len(re.findall(r'^axiom ',external,re.M))==4
 assert not re.search(r'^\s*(axiom|opaque)\b',new,re.M)
 record={'generated_funs_sha256':sha(raw.encode()),'generated_template_sha256':sha(external.encode()),'bound_model_source':str(source.relative_to(R)),'bound_model_sha256':sha(source.read_bytes()),'body_replacements':replacements,'grouping_only_changes':['some(mark) -> some mark','(error) -> error'],'full_first_body_equal_after_boundary_binding':True,'generated_signature':oldsig.strip(),'parametric_signature':newsig.strip(),'four_opaque_globals_eliminated':{'decoder':'checked actual AspisR1TerminalDecoder decoder plus fixed fromStatement carrier transport','tx1':'explicit universally quantified downstream continuation','mark':'explicit universally quantified callback, passed as some mark','error':'explicit universally quantified effectful error mapper'},'error_carriers':'Diagnostic DecodeError/ProgramError/downstream Error are replaced by actual decoder error/generic E/generic F. Closure still ignores decoder error and returns invalidAccountData; errors cannot manufacture success. No SDK/runtime type-refinement theorem is asserted.','selector':'generated selector body byte-token-identical to the checked actual preparation selector; actual_selector_eq fixes the returned public to the same decoded statement','scope':'Actual emitted first control-flow prefix interpreted with fixed checked decoder+selector and arbitrary explicit downstream functions. No downstream tx1/refinement/custody claim or axiom is introduced.'}
 a.out.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print('PASS complete emitted first body; fixed checked decoder/selector; all4globals explicitly bound, no axiom')
if __name__=='__main__':main()
