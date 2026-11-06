from NLF_formal import run
mods=['NLF_FlagSemantics','NLF_WrapperFlagLaws','NLF_SharedDataLaw','NLF_ExclusiveDataLaw','NLF_SharedLamportsLaw','NLF_ExclusiveLamportsLaw','NLF_DataLenLaw','NLF_LamportsLaw']
for i,m in enumerate(mods,40):
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
