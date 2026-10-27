from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
S=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src/crates/aspis-r1-cost-probe/src')
selections=[('verifier.rs','prepared_claim'),('verifier.rs','echeck'),('verifier.rs','put'),('verifier.rs','put_k'),('candidate.rs','wide_view')]
out=[];rows=[]
for file,name in selections:
 p=S/file;src=p.read_text();start=src.index('fn '+name+'(') if 'fn '+name+'(' in src else src.index('fn '+name+'<')
 end=src.index('{',start);depth=1;end+=1
 while depth:
  depth+=(src[end]=='{')-(src[end]=='}');end+=1
 body=src[start:end];out.append(body.replace('fn '+name,'fn XRe_shipped_'+name,1))
 rows.append(dict(file=str(p),file_sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),function=name,first_line=src[:start].count('\n')+1,last_line=src[:end].count('\n')+1,verbatim_function_sha256=hashlib.sha256(body.encode()).hexdigest(),only_edit='function name prefixed XRe_shipped_; same crate helper paths reexport actual library modules'))
(B/'XRe_actual.rs').write_text('\n\n'.join(out)+'\n')
(B/'XRe_actual_source_map.json').write_text(json.dumps(rows,indent=2)+'\n')
