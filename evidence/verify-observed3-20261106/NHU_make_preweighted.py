from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';s=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode();rows=[]
for suffix in ['', '_shared_selector']:
 name='add_preweighted'+suffix;st=s.index('fn '+name+'<');op=s.index('{',st);d=1;i=op+1
 while d:
  d+=(s[i]=='{')-(s[i]=='}');i+=1
 body=s[op+1:i-1];loopstart=body.index('    for group in first..=last {')+len('    for group in first..=last {');original=body[loopstart:body.rindex('\n    }')]
 changed=original.replace('qm31_pack_base4(&lanes)','pack_cut(&lanes,log)')
 if suffix:changed=changed.replace('selector.mul(pack_cut(&lanes,log))','shared_cut(selector,pack_cut(&lanes,log),log)')
 reverse=changed.replace('shared_cut(selector,pack_cut(&lanes,log),log)','selector.mul(pack_cut(&lanes,log))').replace('pack_cut(&lanes,log)','qm31_pack_base4(&lanes)');assert reverse==original
 out='fn NHU_preweighted'+suffix+'_cut<const N:usize>(packed:&mut [QM31;24],start:usize,values:&[QM31;N],'+('selector:QM31,' if suffix else '')+'iter:&mut core::ops::RangeInclusive<usize>,log:&mut PackLog){if let Some(group)=iter.next(){'+changed+'\n}}\n'
 f='NHU_preweighted'+suffix+'_body.rs.txt';(E/f).write_text(out);rows.append(dict(name=name,body_sha256=hashlib.sha256(body.encode()).hexdigest(),loop_sha256=hashlib.sha256(original.encode()).hexdigest(),file=f,status='PASS'))
(E/'NHU_PREWEIGHTED_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,source_sha256=hashlib.sha256(s.encode()).hexdigest(),rows=rows,method='one real RangeInclusive iteration on arbitrary active/exhausted invariant prestate; field child calls only local opaque records'),indent=1)+'\n')
