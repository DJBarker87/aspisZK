from pathlib import Path
import re,json,hashlib
E=Path('evidence/pv-batch2-20261027/extraction');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
t=(E/'raw-249/Types.lean').read_text();f=(E/'raw-249/Funs.lean').read_text();g=(E/'raw-250/Funs.lean').read_text()
# Preserve raw declaration text with only an import-path fix for the private overlay.
(L/'PV_B2_RawSamplerTypes.lean').write_text(t+'\n'+''.join('#print axioms PV_B2_249.'+d+'\n' for d in re.findall(r'^(?:def|structure|inductive) ([\w.]+)',t,re.M)))
(L/'PV_B2_RawSamplerFuns.lean').write_text(f.replace('import PVB2249.Types','import R1Z.PV_B2_RawSamplerTypes')+'\n'+''.join('#print axioms PV_B2_249.'+d+'\n' for d in re.findall(r'^def ([\w.]+)',f,re.M)))
# Reuse the dictionary's exact scalar carriers. There is no field arithmetic substitution.
a='\n'.join('abbrev aspis_core.field.'+n+' := ProverRwFull.aspis_core.field.'+n for n in ['M31','CM31','QM31','wide_exact.WideExact'])+'\n'
x=f.replace('import PVB2249.Types','import R1Z.ProverRwFullTypes').replace('namespace PV_B2_249','namespace PV_B2_Sampler').replace('end PV_B2_249','end PV_B2_Sampler')
x=x.replace('namespace PV_B2_Sampler','namespace PV_B2_Sampler\n'+a,1)
ordinary=re.search(r'def host_sampler.ordinary_sample\n.*?(?=\nend PV_B2_250)',g,re.S)[0]
x=x.replace('end PV_B2_Sampler',ordinary+'\nend PV_B2_Sampler')
x+='\n'+''.join('#print axioms PV_B2_Sampler.'+d+'\n' for d in re.findall(r'^def ([\w.]+)',x,re.M))
(L/'PV_B2_Sampler.lean').write_text(x)
(E/'sampler-adaptation.json').write_text(json.dumps(dict(import_only_raw='RawSamplerFuns: PVB2249.Types → R1Z.PV_B2_RawSamplerTypes',normalized='PV_B2_Sampler reuses ProverRwFull scalar structures through abbreviations; namespace renamed; ordinary root appended from raw250; shared helpers emitted once',raw_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [E/'raw-249/Funs.lean',E/'raw-249/Types.lean',E/'raw-250/Funs.lean']},no_body_rewrite=True),indent=2)+'\n')
