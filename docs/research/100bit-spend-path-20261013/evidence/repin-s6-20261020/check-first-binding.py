#!/usr/bin/env python3
"""Recheck complete emitted caller bodies under explicit historical boundary binding."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;B=E.parents[1];R=B.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
generated=E/'extraction-first/generated/AspisR1S6/Funs.lean';model=B/'lean/RepinS6First.lean'
g=generated.read_text();m=model.read_text()
def body(s,name):
 start=re.search(r'^def '+name+r'(?:\s|\{)',s,re.M).start()
 ends=[s.find(x,start+1) for x in ['\n/--','\ndef ','\nend ']]
 end=min(x for x in ends if x>=0)
 return s[start:end].split(':= do',1)[1].strip()
def compact(s):return re.sub(r'\s+','',s).replace('(error)','error')
mappings={
 'first':[
 ('aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1','decode'),
 ('first.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError','(decodeErrorClosure invalidAccountData)'),
 ('aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public','pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public'),
 ('solana_program_error.ProgramError','E'),('first_decoded p','first_decoded tx1 error p'),('Std.U8','U8')],
 'first_decoded':[
 ('aspis_r1_cost_probe.verifier.candidate.tx1\n      SolanaDigest.Insts.Aspis_coreDigestDigest32','tx1'),
 ('aspis_r1_cost_probe.verifier.Error','F'),('solana_program_error.ProgramError','E')],
 'observer':[]}
checks=[]
for name,replacements in mappings.items():
 s=body(g,name)
 for a,b in replacements:
  assert a in s,(name,a);s=s.replace(a,b)
 assert compact(s)==compact(body(m,name)),(name,s,body(m,name))
 checks.append({'declaration':name,'complete_body_equal_after_binding':True,'replacements':replacements})
# Actual generated decode-error closure returns precisely InvalidAccountData,
# ignoring the decoded error. No invocation of a fabricated error function.
closure=g.split('first.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once',1)[1].split(':= do',1)[1].split('/--',1)[0].strip()
assert closure=='ok solana_program_error.ProgramError.InvalidAccountData'
# Historical fixed carriers/selector are still exact Rust declarations.
pins=json.loads((B/'tools/public-preparation-extraction-kit/source-pins.json').read_text())
carriers=[]
for c in pins['cuts']:
 if not c['path'].startswith('crates/aspis-statement/'):continue
 if c['name'] in ['r0_error']:continue
 fragment=B/'tools/public-preparation-extraction-kit/fragments'/(c['name']+'.rs')
 raw=subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+c['path']])
 assert fragment.read_bytes() in raw,c['name']
 carriers.append({'name':c['name'],'source_path':c['path'],'sha256':sha(fragment),'exact_declaration_retained':True})
terminal='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
# The entire decoder/statement file is identical to the historical first pin.
old=subprocess.check_output(['git','-C',str(R),'show','ebe378259fb7d9c8a007eec2c8a8eb4850e549fc:'+terminal])
current=subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+terminal]);assert old==current
result=dict(generated_funs_sha256=sha(generated),model_sha256=sha(model),checks=checks,decode_error_closure_preserved=True,retained_statement_declarations=carriers,decoder_statement_file=dict(path=terminal,sha256=hashlib.sha256(current).hexdigest(),historical_first_revision='ebe378259fb7d9c8a007eec2c8a8eb4850e549fc',frozen_revision='b2727acd3abf79315d18b754a260f58f4b1c6326',whole_file_identical=True),boundaries={'decoder':'checked actual decoder plus fromStatement transport, as in historical FirstCaller.decode','selector':'checked actual preparation selector on retained fixed carriers','tx1':'explicit universal continuation; digest trait is supplied by the actual generated call, unit digest carrier retained','error':'explicit universal effectful mapper; cannot manufacture success','ProgramError':'generic E; invalidAccountData preserves the generated constant branch','observer':'complete emitted release body ok none'},scope='Complete control-flow interpretation; no SDK carrier/runtime or downstream tx1 refinement theorem.')
(E/'first-binding-check.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS full frozen first, first_decoded, observer and retained statement/decoder boundaries')
