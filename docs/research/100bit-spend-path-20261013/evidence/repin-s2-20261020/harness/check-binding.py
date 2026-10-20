#!/usr/bin/env python3
"""Fail-closed token audit of explicit boundary interpretation (not Rust refinement)."""
from pathlib import Path
import hashlib,json,re,difflib
R=Path(__file__).resolve().parents[1]
G=R/'generated-first/AspisR1S2First/Funs.lean'
M=R.parents[1]/'lean/S2ObserverOffRepin.lean'
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def body(s,name):
 match=re.search(r'^def '+re.escape(name)+r'\b[\s\S]*?:= do\n',s,re.M)
 assert match,name
 start=match.end(); end=re.search(r'\n(?:/--|end )',s[start:]);return s[start:start+end.start()] if end else s[start:]
subs={
 'observer':{},
 'first_decoded':{
 'aspis_r1_cost_probe.verifier.candidate.tx1\n      SolanaDigest.Insts.Aspis_coreDigestDigest32':'tx1',
 'aspis_r1_cost_probe.verifier.Error':'F',
 'solana_program_error.ProgramError':'E',
 '(error)':'error',
 'let o ←':'let obs ←',
 '() o':'() obs',
 'public1 public_bytes':'selected public_bytes',
 },
 'first':{
 'aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1':'decode',
 'first.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError':'(decodeErrorClosure invalidAccountData)',
 'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public':'AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public',
 'let p ←':'let public1 ←',
 'first_decoded p':'first_decoded tx1 error public1',
 'solana_program_error.ProgramError':'E',
 'Std.U8':'U8',
 }}
rows=[]
for name,replacements in subs.items():
 g=body(G.read_text(),name);m=body(M.read_text(),name); bound=g
 for a,b in replacements.items():
  assert a in bound,(name,a)
  bound=bound.replace(a,b)
 norm=lambda s:re.sub(r'\s+','',s)
 same=norm(bound)==norm(m)
 rows.append(dict(name=name,generated_body_sha256=sha(g),model_body_sha256=sha(m),substitutions=replacements,body_equal_after_binding=same))
 if not same:
  print(name);print('\n'.join(difflib.unified_diff(bound.splitlines(),m.splitlines())))
report=dict(scope='Explicit boundary interpretation; not SDK/type/runtime or downstream-refinement theorem',generated_sha256=sha(G.read_text()),model_sha256=sha(M.read_text()),declarations=rows,all_equal=all(r['body_equal_after_binding'] for r in rows))
(R/'binding-audit.json').write_text(json.dumps(report,indent=2)+'\n')
assert report['all_equal']
print('observer, first_decoded, first: exact body token matches after listed bindings')
