from NLF_formal import *
for i,name in [(65,'NLF_COMBINED_IMPORT'),(66,'NLF_ProofDriver'),(67,'NLF_ScanDriver')]:
 r=run(f'NLF_L{i:03d}','lean',name)
 assert r['exit_status']==0,name
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for i,name in [(68,'NLF_ProofDriver'),(69,'NLF_ScanDriver')]:
 r=ssh('cat '+B+'/NLF_native/'+name+'.c');assert r.returncode==0
 files={'NLF_native/'+name+'.c':r.stdout}
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  files['NLF_native/'+n]=lzma.decompress((E/('NLF_'+n+'.xz')).read_bytes()).decode()
 r=run(f'NLF_L{i:03d}','link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLF_native/'+name,*files],files)
 assert r['exit_status']==0,name
