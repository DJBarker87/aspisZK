from pathlib import Path
import json,difflib,hashlib
E=Path(__file__).resolve().parent
mods=['RPx_Deployed','NFM_ProductInstance','NFG_QueryLoopSource','NFG_PushRoot','NFN_GeometryPart08','NFS_AccumPart02']+json.loads((E.parent/'slice-q-values-20261104/NFP_AUDIT_ROOTS.json').read_text())['modules']
roots=['NFS_NEV_AccumPacket.raw_length','NFS_NEV_AccumPacket.result_state_effects','NFS_NEV_AccumPacket.no_base_dependency','NFS_NEV_AccumulateComplete.reference','NFS_NEV_AccumulateComplete.native','AspisR1.RPx_Deployed.deployed','AspisR1.NFM_ProductInstance.installed','AspisR1.NFM_ProductInstance.wrapper','AspisR1.NFG_QueryLoopSource.complete','NFN_NFB_GeometryComposed.result_state_effects','AspisR1.NFP_QueryTrace.erased','AspisR1.NFP_LoopTransport.complete']
(E/'NFS_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in mods)+''.join('#print axioms '+r+'\n' for r in roots))
source=(E.parent/'slice-q-phase-20261104/NFN_ProofDriver.lean').read_text()
begin=source.index('    if mode == "proof0" then');end=source.index('    else if mode == "fixtures" then',begin)
groups=[roots[i:i+4] for i in range(0,len(roots),4)]
select=''
for i,rs in enumerate(groups):
 select+=('    if' if i==0 else '    else if')+f' mode == "proof{i}" then\n      (#[`NFS_COMBINED_IMPORT], #['+', '.join('`'+r for r in rs)+'])\n'
# Preserve accepted pre-runtime prefix and the raw action exactly.
driver=source[:begin]+select+source[end:]
(E/'NFS_ProofDriver.lean').write_text(driver)
(E/'NFS_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff(source.splitlines(True),driver.splitlines(True),fromfile='NFN_ProofDriver.lean',tofile='NFS_ProofDriver.lean')))
(E/'NFS_AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=mods,roots=roots,groups=groups),indent=1)+'\n')
scanner=(E.parent/'slice-q-phase-20261104/NFN_Driver.lean').read_text().replace('NFN_COMBINED_IMPORT','NFS_COMBINED_IMPORT').replace('NFN_EXPECTED_IMPORTS','NFS_EXPECTED_IMPORTS').replace('NFN_LOADED_scan','NFS_LOADED_scan')
(E/'NFS_Driver.lean').write_text(scanner)
g={r['module']:r['imports'] for r in map(json.loads,(E.parent/'slice-q-phase-20261104/NFN_QUERY_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for row in map(json.loads,(E.parent/'slice-q-values-20261104/NFP_EXPECTED_IMPORTS.jsonl').read_text().splitlines()):g[row['module']]=row['imports']
for n,r in json.loads((E/'NFS_SOURCE_GRAPH.json').read_text()).items():
 if not r.get('missing') and n not in g:g[n]=list(dict.fromkeys(['Init']+r['imports']))
for p in E.glob('NFS_*.lean'):g[p.stem]=list(dict.fromkeys(['Init']+[m for l in p.read_text().splitlines() if l.startswith('import ') for m in l[7:].split() if m!='all']))
(E/'NFS_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=im))+'\n' for n,im in sorted(g.items())))
# Paths select only our own cache, never edit fixtures.
C='/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104'
(E/'NFS_FIXTURE_PATHS.json').write_text(json.dumps([C+'/fixtures'])+'\n')
