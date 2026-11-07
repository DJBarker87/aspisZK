from NNE_formal import *
old=json.loads((E/'NNE_AUDIT_MODULES.json').read_text())[0]
new=json.loads((E/'NNE_RESUME_MODULES.json').read_text())
mods=list(dict.fromkeys(old+new+['NNE_COMBINED_IMPORT','NNE_RESUME_COMBINED_IMPORT',
 'TCK_WeakRoot0','TAS_Interfaces','TAS_Top','TFM_TopExact']))
(E/'NNE_EXPORT_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
r=run('NNE_L098','inspect','retention',['python3','NNE_finalize_host.py'],
 {n:(E/n).read_text() for n in ['NNE_finalize_host.py','NNE_EXPORT_MODULES.json']})
sys.exit(r['exit_status'])
