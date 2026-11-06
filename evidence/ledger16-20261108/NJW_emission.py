from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;S=E.parent/'tx2-decoders-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
raw=S/'NJI_EMITTED/raw/NJI_Extracted/Funs.lean';original=raw.read_text();rows=[]
for rid,leaf,file,chain in[
 ('TX2:150','aspis_statement.pool_v1.format.decode_verifier_policy_v1','Core',['NJI_PolicyTotal.native_source','NJI_PolicyParser.raw','NJI_Extracted.aspis_statement.pool_v1.format.decode_verifier_policy_v1']),
 ('TX2:157','aspis_statement.pool_v1.pair_forest_accounts.validate_master','Master',['NJI_MasterCut.native_source','NJI_MasterModel.raw','NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master']),
 ('TX2:206','aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1','Core',['NJI_V1Join.entry_source','NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1']),
 ('TX2:208','aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1','Core',['NJI_V1Join.registry_source','NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1'])]:
 p=S/f'NJI_Extracted.{file}.lean';s=p.read_text()
 pat=r'(?m)^def\s+'+re.escape(leaf)+r'\s*\('
 m=re.search(pat,s);r=re.search(pat,original);assert m and r,(rid,leaf)
 def body(t,start):
  q=re.search(r'(?m)^(?:def |end |end$|/-\*|/--)',t[start+4:]);return t[start:start+4+q.start()]if q else t[start:]
 decl=body(s,m.start());rawdecl=body(original,r.start())
 assert ':='in decl and not re.search(r'\b(axiom|opaque|sorry|admit|sorryAx)\b',decl)
 rows.append(dict(row=rid,definition='NJI_Extracted.'+leaf,emitted=True,template=False,opaque=False,raw_emitted_file=str(raw),raw_file_sha256=H(raw.read_bytes()),raw_declaration_sha256=H(rawdecl.encode()),selected_source=str(p),selected_file_sha256=H(p.read_bytes()),selected_declaration_sha256=H(decl.encode()),root_definition_chain=chain,exact_selected_declaration=decl,parameterization='Explicit resolved concrete callee parameters; instantiated internally by root, never external template axioms. Review source SCC parameter propagation in NJI diffs.'))
missing=['decode_pair_forest_checkpoint_v1','decode_pair_forest_master_v1','decode_verifier_registry_entry_v1','decode_verifier_registry_v1']
(E/'NJW_NJI_EMISSION.json').write_text(json.dumps(dict(status='PASS_FOUR_CANDIDATE_BODIES_EMITTED',rows=rows,finding='NJI-F1 four omitted decoder bodies concern OTHER OPEN rows TX2:152/153/201/203. No opaque/template body substitutes for these candidates.',omitted_decoder_names=missing,compiled_template=False),indent=1)+'\n')
print(json.dumps(dict(stage='emission',candidates_checked=len(rows),opaque_or_template=0)))
