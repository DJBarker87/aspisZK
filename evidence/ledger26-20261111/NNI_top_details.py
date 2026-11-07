from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;p=E/'NNI_TOP_COMPOSITION.json';x=json.loads(p.read_text());files=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
terms={'TOP:G1a':('NNC_G1a.assemble','NNC_G1a',['nativeRep','headerRep']),'TOP:G1b':('NMV_TasRoots.field240 / NNF_TAS.roots','NMV_TasRoots',['canonical241 root','same library/implementation instantiation','canonical344/240 roots for NNF_ folds']),'TOP:R0rep':('NNC_R0Rep.assemble','NNC_R0Rep',['selected']),'TOP:G2':('NMV_TasRoots.packet.g2','NMV_TasRoots',['canonical host library/implementation instantiation','required NoWrite repair replay; pl itself has concrete LIBB_PoolNoWrite.laws support']),'TOP:A3':('NNE_RecordSig.a3','NNE_RecordSig',['host S0','A1','A2']),'TOP:A4':('NNE_RecordSig.a4','NNE_RecordSig',['host S0','A1','A2']),'TOP:A5':('NNE_RecordSig.a5','NNE_RecordSig',['host S0','A1','A2']),'TOP:EntryRep':('TAS_TopB_NNE.top_splitB_counts','TAS_TopB_NNE',['host G0 instantiation; stand-in/local status only'])}
for r in x['top_composition_obligations']:
 if r['id']in terms:
  term,module,extra=terms[r['id']];paths=[f for f in files if f.endswith('/'+module+'.lean')and '/sources/'not in f];assert paths,module;path=min(paths,key=len);commit=subprocess.check_output(['git','log','-1','--format=%H','--',path],text=True).strip();r.update(deliverable=dict(lean=term,commit=commit,source=path,kind='uninstantiated builder/support; not an exact closed host field'),extra_parameters=extra,status='CANDIDATE',print_axioms=None)
 if r['id']=='TOP:A1':r['interface_field']='TAS.NND_A1; associated Sig.Exhibited'
 if r['id']=='TOP:A2':r['interface_field']='TAS.NND_A2; associated Sig.Exhibited'
 if r['id']in ['TOP:A3','TOP:A4','TOP:A5']:r['interface_field']='TAS.NNE_'+r['id'].split(':')[1]
x['PoolLaws_available_term']='LIBB_PoolNoWrite.laws : NMV_NoWrite.PoolLaws LIBB_PoolLib.library; exact statement recorded in NNI_L010; credit only after all-root gate'
p.write_text(json.dumps(x,indent=1)+'\n');print('Top builders, source commits and pending parameters recorded; no top closure assigned')
