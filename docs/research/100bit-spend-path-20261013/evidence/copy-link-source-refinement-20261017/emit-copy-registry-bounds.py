from pathlib import Path
import re,json,hashlib
root=Path('/tmp');source=(root/'CopyLinkLoopSource.lean').read_text();matches=list(re.finditer(r'(?m)^    \{\n      tag := .*?^    \}',source,re.S));assert len(matches)==136,len(matches);records=[m.group() for m in matches]
old=(root/'CopyRegistryBounds.lean').read_text();header=old[:old.index('theorem registry_valid')]
chunks=[records[i:i+16] for i in range(0,136,16)]
text=header
for i,chunk in enumerate(chunks):text+=f'private def chunk_{i} : List Raw := [\n'+',\n'.join(chunk)+'\n  ]\n\n'
for i,chunk in enumerate(chunks):text+=f'private theorem chunk_{i}_valid : List.Forall DescriptorValid chunk_{i} := by\n  decide\n\n'
end='''private theorem forall_append (a b : List Raw)
    (ha : List.Forall DescriptorValid a) (hb : List.Forall DescriptorValid b) :
    List.Forall DescriptorValid (a ++ b) := by
  rw [List.forall_iff_forall_mem] at *
  intro link hmem
  rcases List.mem_append.mp hmem with h | h
  · exact ha link h
  · exact hb link h

'''
text+=end
append=' ++ '.join(f'chunk_{i}' for i in range(len(chunks)))
text+=f'private theorem registry_chunks : registry.val = {append} := by\n  unfold registry AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS '+ ' '.join(f'chunk_{i}' for i in range(len(chunks))) + '\n  rfl\n\ntheorem registry_valid : List.Forall DescriptorValid registry.val := by\n  rw [registry_chunks]\n'
proof='chunk_0_valid'
for i in range(1,9):proof=f'forall_append _ _ ({proof}) chunk_{i}_valid'
text+='  exact '+proof+'\n\n'
text+=old[old.index('theorem member_bounds'):]
full=root/'CopyRegistryBounds-chunked.lean';full.write_text(text)
pre=header+f'private def chunk_0 : List Raw := [\n'+',\n'.join(chunks[0])+'\n  ]\n\ntheorem first_chunk_valid : List.Forall DescriptorValid chunk_0 := by\n  decide\n\n#print axioms first_chunk_valid\nend AspisR1.CopyRegistryBounds\n'
(root/'CopyRegistryBounds-preflight.lean').write_text(pre)
manifest={'exact_source_sha256':hashlib.sha256(source.encode()).hexdigest(),'record_count':len(records),'chunk_sizes':[len(c) for c in chunks],'ordered_literal_records_preserved':True,'record_sha256':[hashlib.sha256(r.encode()).hexdigest() for r in records],'full_sha256':hashlib.sha256(text.encode()).hexdigest(),'preflight_sha256':hashlib.sha256(pre.encode()).hexdigest(),'replacement':'One136-record Forall decide hit default recursion depth; named16-record independent facts plus symbolic Forall append, no cap/recursion/heartbeat increase.'}
(root/'CopyRegistryBounds.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:v for k,v in manifest.items() if k!='record_sha256'},indent=2))
