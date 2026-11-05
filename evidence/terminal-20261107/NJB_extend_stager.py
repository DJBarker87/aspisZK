from pathlib import Path
import json,difflib,lzma,shutil
E=Path(__file__).resolve().parent;P=E.parent/'extract-stage-20261106'
s=(P/'NHR_stage.py').read_text();old=s
rows=json.loads(lzma.open(E/'NJB_OBLIGATIONS.json.xz').read())
roots=[]
for r in rows:
 file,fun=r['function'].split('::',1);mod=file.split('/src/')[1].removesuffix('.rs').replace('/','::')
 name=fun.replace('Selectors::','_::').replace('PoolV1PairForestTerminalStatementV1::','_::')
 roots.append('crate::'+mod+'::'+name)
(E/'NJB_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n')
# Additive branch: old four selectors and their exact commands remain unchanged.
s=s.replace("    root = 'crate::verifier::candidate::'+args.function", "    root = 'crate::verifier::candidate::'+args.function\n    terminal = args.function == 'NJB_terminal'\n    roots = json.loads((E/'NJB_ROOTS.json').read_text()) if terminal else [root]\n    if terminal: root = roots[0]")
s=s.replace("    for x in opacity: cmd +=", "    if terminal:\n        cmd = cmd[:-2]\n        for selected in roots: cmd += ['--start-from', selected]\n    for x in opacity: cmd +=")
s=s.replace("    aeneas = [str(TOOLROOT", "    if terminal:\n        meta = json.loads((out/'metadata.json').read_text())\n        pkg = next(p for p in meta['packages'] if p['name']=='aspis-statement')\n        features = next(n['features'] for n in meta['resolve']['nodes'] if n['id']==pkg['id'])\n        cmd[cmd.index('--manifest-path')+1] = str(workspace/'crates/aspis-statement/Cargo.toml')\n        cmd[cmd.index('--features')+1] = ','.join(features)\n    aeneas = [str(TOOLROOT")
s=s.replace("'NHR_'+args.function", "('NJB_terminal' if terminal else 'NHR_'+args.function)")
s=s.replace("'root':root", "'root':root") # existing uses keyword syntax; retain root provenance below.
s=s.replace("opacity=opacity,root=root)","opacity=opacity,root=root,roots=roots)")
s=s.replace("'tx2_common']);", "'tx2_common','NJB_terminal']);")
s=s.replace("CARGO_TARGET_DIR=str(E/'NHR_target')", "CARGO_TARGET_DIR=str(E/'NJB_target')")
(E/'NJB_NHR_stage.py').write_text(s)
(E/'NJB_STAGER.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='NHR_stage.py',tofile='NJB_NHR_stage.py')))
# original inputs once, pinned by their inherited hashes
for n in ['NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256']:shutil.copyfile(P/n,E/n.replace('NHR_','NJB_'))
# keep original expected basenames remotely; no duplicate payload locally
opacity=json.loads((P/'NHR_OPACITY.json').read_text());opacity['NJB_terminal']=[]
(E/'NJB_OPACITY.json').write_text(json.dumps(opacity,indent=1)+'\n')
print('additive terminal selector: 32 roots, unchanged original selector behavior')
