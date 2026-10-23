from pathlib import Path
import subprocess, hashlib, json
R=Path(__file__).resolve().parents[5]
E=Path(__file__).resolve().parent
base=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
paths=['crates/aspis-r1-cost-probe/src/'+p for p in ['host_semantic.rs','host_sumcheck.rs','r1_wire.rs','transcript.rs','prover.rs','weights.rs','compact.rs']]
# Historical bodies must match, not just theorem/helper names.
refs={'part28':'f53e30fc4e26375c1bd0623532dafaf49571dc9d','part48':'617fc58aaf','part55':'341584654f'}
def sha(b):return hashlib.sha256(b).hexdigest()
rows=[]
for p in paths:
 b=(R/p).read_bytes(); same={}
 for k,rev in refs.items():
  old=subprocess.check_output(['git','show',rev+':'+p],cwd=R)
  same[k]={'sha256':sha(old),'whole_file_identical':old==b}
 rows.append(dict(path=p,sha256=sha(b),size=len(b),historical=same))
w=(R/paths[2]).read_text()
s=(R/paths[0]).read_text()
assert 'let value = transcript.semantic(row, &framed)?;\n            bytes.extend_from_slice(&framed);' in s
out={'source_revision':base,'files':rows,'scope':'source identity only, no compilation or theorem discharge','caller':'host_semantic::build_with_helper_mode scalar closure -> r1_wire::SemanticTranscript::semantic','retained_contracts':['R1Z.ProverCommitInit28.source','R1Z.ProverCommitSemanticSource28.sample','R1Z.ProverCommitSemanticSource28.semantic','R1Z.ProverCommitFields29.bounded_owned'],'reuse_limits':'sim::walk owner and simulator tape do not identify the real caller; parts47-55 used only at source-identical helpers'}
(E/'RealR3_source-identity.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({r['path']:{k:v['whole_file_identical'] for k,v in r['historical'].items()} for r in rows},indent=2))
