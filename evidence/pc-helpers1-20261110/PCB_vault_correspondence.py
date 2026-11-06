"""Checked field-for-field carrier/projection correspondence, with mutations."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;REV='b936275465600469312d1f058cdc91ea2a11f3dc'
def block(s,needle):
 a=s.index(needle);a=s.index('{',a);level=0
 for b in range(a,len(s)):
  level += (s[b]=='{')-(s[b]=='}')
  if level==0:return s[a:b+1]
 raise AssertionError('unclosed source')
def fields(s,name):return re.findall(r'pub\s+(\w+)\s*:\s*(u8)',block(s,'struct '+name))
def tokens(s):return re.findall(r'\w+|[^\s]',re.sub(r',\s*}', '}',s))
native_input=subprocess.check_output(['git','show',REV+':programs/aspis-pool/src/pair_forest.rs'],text=True)
native_output=subprocess.check_output(['git','show',REV+':programs/aspis-pool/src/vault.rs'],text=True)
ref=(E/'PCB_vault_reference.rs').read_text();actual_ref=(E/'PCB_300.rs').read_text()
actual=block(native_input,'fn vault(').replace('self.','h.')
def valid(ref):
 return fields(native_input,'PoolV1PairForestTerminalBumpHintsV1')==fields(ref,'PoolV1PairForestTerminalBumpHintsV1') and fields(native_output,'VaultBumpHintsV1')==fields(ref,'VaultBumpHintsV1') and tokens(actual)==tokens(block(ref,'fn reference(')) and tokens(actual)==tokens(block(actual_ref,'fn reference('))
assert valid(ref)
mutants=[ref.replace('h.vault_authority','h.current_page'),ref.replace('h.vault_token_account','h.next_page'),ref.replace('pub current_page:u8','pub current_page:u16'),ref.replace('pub vault_authority:u8','pub wrong_authority:u8'),ref.replace('h.vault_authority','0')]
assert all(not valid(m) for m in mutants)
(E/'PCB_300_CORRESPONDENCE.json').write_text(json.dumps(dict(status='PASS',reviewed_transcription='PCB-RT-300-carriers (option-A P6/D188 reclassification after E004 dependency compilation timeout)',native_revision=REV,input_fields=fields(native_input,'PoolV1PairForestTerminalBumpHintsV1'),output_fields=fields(native_output,'VaultBumpHintsV1'),projection_tokens=tokens(actual),native_reference_body_identical=True,isolated_reference_body_identical=True,semantic_map='identity on all labelled u8 fields; no ABI/layout equality asserted',mutations_rejected=len(mutants),mutations_tested=mutants,reference_sha256=hashlib.sha256(ref.encode()).hexdigest(),failed_full_extraction='PCB_E004',isolated_extraction='PCB_E005',native_positive='PCB_K055',native_inverse='PCB_K056',fidelity=['PCB_K041','PCB_K042','PCB_K043','PCB_K044']),indent=1)+'\n')
print('PCB vault correspondence PASS; five carrier/projection mutations rejected')
