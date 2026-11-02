"""Resolve four conservative inventory targets by frozen receiver types, before pruning."""
import subprocess,hashlib
F='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1'
TARGETS=['crates/aspis-core/src/field.rs::M31::to_le_bytes','crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind']
def validate(c,expected,b,v):
 try:
  q=c['encoder_alternative'];g=q['excluded'];assert g in TARGETS and expected==F+' -> '+g
  assert c['kind']=='alternative-resolution' and q['function']==F and q['trust_classification']=='P6/D188 option A reclassification'
  assert q['method']=='frozen receiver type resolution; compile entire unchanged caller with NEM_K102; retained native associations separate'
  source=subprocess.check_output(['git','show',b['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True)
  a=source.index('pub fn '+F.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['source_sha256']==hashlib.sha256(source.encode()).hexdigest()
  assert 'pub checkpoint_sequence: u64,' in source and 'statement: &PoolV1PairForestTerminalStatementV1,' in body
  assert 'output[5] = statement.transition_kind() as u8;' in body and '&common.checkpoint_sequence.to_le_bytes()' in body
  assert q['actual_receivers']==['&PoolV1PairForestTerminalStatementV1','u64'] and q['not_a_native_root_pass']
  assert v.native_pair('NEM_K102','NEM_K103')
  from NEM_artifacts import native_support
  assert q['native_support']==native_support(['NEM_K102','NEM_K103'])
  for r in q['native_support']:v.inherited.artifact(r)
  patch=(v.E/'NEM_K102-NEM_native_contracts.patch').read_text();assert 'let kind=s.transition_kind();' in patch
  # This patch only appends a cfg(kani) module to the unchanged, compiler-typechecked file.
  import difflib
  hook='\n#[cfg(kani)]\n#[path="NEM_kind_call.rs"]\nmod NEM_kind_call;\n'
  exact=''.join(difflib.unified_diff(source.splitlines(True),(source+hook).splitlines(True),fromfile='a/'+F.split('::')[0],tofile='b/'+F.split('::')[0]))
  assert patch.startswith(exact+'--- /dev/null\n')
  assert [t['name'] for t in q['theorems']]==['NEM_KindInstance.statement_window','NEM_EncoderReceiver.sequence_width'] and all(v.inherited.theorem(t) for t in q['theorems'])
  return True
 except (KeyError,AssertionError,OSError,ValueError,TypeError):return False
