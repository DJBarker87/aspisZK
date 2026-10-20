from pathlib import Path
import hashlib,json
p=Path(__file__).parent/'input/fragments/stage2_resume.rs'; s=p.read_text(); q=Path(__file__).parent/'input/fragments/stage2_resume_prefix.rs'; t=q.read_text()
needle="let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];\n    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.k()?;"
assert s.count(needle)==1 and needle in t
assert t.index(needle)<t.index('Ok((state,roots,gamma,kappa,alpha,rho,r.at))')
print(json.dumps({'source_fragment_sha256':hashlib.sha256(s.encode()).hexdigest(),'cut_sha256':hashlib.sha256(needle.encode()).hexdigest(),'shim_fragment_sha256':hashlib.sha256(t.encode()).hexdigest(),'cut_present_once':True,'return_follows_cut':True},indent=2))
