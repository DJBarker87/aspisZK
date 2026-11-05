from NIS_formal import *
for i,name in enumerate(['NIS_SnapshotAbi','NIS_SdkReads','NIS_AbiFrame','NIS_EntryPrefixes','NIS_OwnedHeaders','NIS_Distinct3'],35):
 run('NIS_L%03d'%i,'lean',name)
