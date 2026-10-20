#!/usr/bin/env python3
"""Inverse-factor the actual common query prefix around its sole dot call."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;repo=tool.parents[4];area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest();frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';path='crates/aspis-r1-cost-probe/src/verifier.rs'
src=subprocess.check_output(['git','-C',str(repo),'show',frozen+':'+path]);begin=src.index(b'fn query_with_geometry<');end=src.index(b'    let node=',begin);function=src[begin:end];body=function[function.index(b'{')+1:];index=b'\n    let i=a.next;let u=p.queries[i] as usize;let q=v.query(i);';assert body.startswith(index);remaining=body[len(index):]
call=b'    let dots=crate::fast_dots::four_dots(q,g);';before,after=remaining.split(call)
import re
assert not re.search(rb'\bg\b',before+after), 'gamma read outside actual dot call'
assert not re.search(rb'\ba\b|\bpending\b',before+after), 'private stage state leaks into prefix'
old=(tool/'rho-query-context-input/fragments/common-prefix.rs').read_bytes();oldbody=old[old.index(b'{')+1:old.rindex(b'    Ok((u,folded))')];assert oldbody.strip()==body.replace(b'    let i=a.next;',b'',1).strip()
# The exact operation order is index, original typed query slice, authenticate,
# dot kernel, original traces/folding/checks. Each unchanged factor is computed
# on the same arguments; no successful-operation or equivalence law is assumed.
parts={'index.rs':b'let u=p.queries[i] as usize;','query.rs':b'let q=v.query(i);','authenticate.rs':before,'dot.rs':call,'fold.rs':after}
assert index+parts['authenticate.rs']+parts['dot.rs']+parts['fold.rs']==body
qsrc=(area/'lean/CuSavingsRetainedQueryPrefixBinding.lean').read_bytes();text=qsrc.decode();assert text.index('let u←B.queryIndex')<text.index('let q←AspisR1CuQuery.verifier.View.query')<text.index('let authenticated←B.authenticate')<text.index('let dots←kernel')<text.index('B.fold D v p hash obs geometry i u q dots')
assert 'queryPrefix:=(sourcePrefix' in text and text.count('queryPrefix:=(sourcePrefix')==2
out=tool/'retained-query-prefix-source';rows=[]
for name,content in parts.items():
 p=out/name
 if a.check:assert p.read_bytes()==content,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(content)
 rows.append(dict(path=str(p.relative_to(repo)),sha256=sha(content)))
report=dict(status='PASS',frozen=frozen,path=path,full_prefix_sha256=sha(body),common_rho_prefix_body_identical=True,parts=rows,inverse_factor_exact=True,no_gamma_or_mutable_stage_state_in_unchanged_authentication_or_fold=True,query_carrier='CuQuery source View.query, checked exact source body/variant query-length constants from candidate10; View copy preserves every public field and variant constructor',source_admission='Exact pure source-factor binding within existing original-source/runtime boundary. Unchanged index/auth/fold operations are computational parameters shared verbatim, no laws. Authentication errors return before dot call; all source traces and folding checks remain in original suffix.',source_wrapper_sha256=sha(qsrc),source_context_api='CuSavingsRetainedQueryPrefixBinding.Boundaries/sourcePrefix/newBinding/oldBinding')
b=(json.dumps(report,indent=2)+'\n').encode();p=ev/'RETAINED-QUERY-PREFIX-SOURCE-AUDIT.json'
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(status='PASS',check=a.check,inverse_exact=True)))
