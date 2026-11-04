"""Use the final five slots to inspect statements, domains and headline premises."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[('NFX_Statement_Q',[
'AspisR1.NFS_QueryValuesPacket.source','AspisR1.NFS_QueryValuesPacket.result','AspisR1.NFS_QueryLoopRoot.tx1','AspisR1.NFS_QueryLoopRoot.tx2','AspisR1.NFS_PacketRoot.query','AspisR1.NFS_PacketRoot.loop']),
('NFX_Statement_Geometry',['NFN_NFB_GeometryComposed.result_state_effects','NFN_NFB_GeometryComposed.accepted_physical','AspisR1.NFM_ProductInstance.installed','AspisR1.NFM_ProductInstance.wrapper']),
('NFX_Statement_DField',['NFQ_FieldLaws.neg_value','NFQ_FieldLaws.cm_reference','NFQ_FieldLaws.qm_reference','NFQ_Reduce.source','NFQ_PreparedMultiplier.source']),
('NFX_Statement_DHelpers',['NFQ_RowShape.reference','NFQ_RowShape.compact_reference','NFQ_Transport.folds_reference','NFQ_Transport.final_len_reference','NFQ_Transport.checkpoint_size_reference','NFQ_Readonly.reference','NFQ_StatementLaws.expected_reference','NFQ_StatementLaws.copied_reference','NFQ_StatementLaws.limbs_reference','NFQ_WideGetters.c0','NFQ_WideGetters.c1']),
('NFX_Statement_Headline',['AspisR1.RPx_Deployed.deployed'])]
for i,(module,roots) in enumerate(jobs,36):
 source='import NFX_COMBINED_IMPORT\n'+'\n'.join('#print '+r+'\n#print axioms '+r for r in roots)+'\n'
 (E/(module+'.lean')).write_text(source)
 a=f'NFX_L{i:03}'
 with (E/(a+'.client.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NFX_run.py'),a,'lean',module],stdout=out,stderr=subprocess.STDOUT)
 print(a,module,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
