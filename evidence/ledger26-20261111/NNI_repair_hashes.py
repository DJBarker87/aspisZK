from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();patch=(E.parent/'top-assembly-20261107/rev2/NMV_REV2_NOWRITE.patch').read_text();rows=[]
parts=re.split(r'(?m)^--- a/',patch)[1:]
for part in parts:
 lines=part.splitlines(True);name=lines[0].strip();old=subprocess.check_output(['git','show','HEAD:'+name]);source=old.decode().splitlines(True);out=[];cursor=0;i=2
 while i<len(lines):
  m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i]);assert m,lines[i]
  start=int(m[1])-1;out+=source[cursor:start];cursor=start;i+=1
  while i<len(lines)and not lines[i].startswith('@@'):
   line=lines[i];i+=1
   if line.startswith(' '):assert source[cursor]==line[1:];out.append(source[cursor]);cursor+=1
   elif line.startswith('-'):assert source[cursor]==line[1:];cursor+=1
   elif line.startswith('+'):out.append(line[1:])
   elif line.startswith('\\'):pass
   else:raise AssertionError(line)
 out+=source[cursor:];new=''.join(out).encode();rows.append(dict(module=Path(name).stem,path=name,old_sha256=H(old),new_sha256=H(new),recipe='Exact NMV_REV2_NOWRITE.patch, strict hunk/context match',new_source_replayed_by_NNI=False,selected_for_row_credit=False))
for m in ['NNC_RSLReads','NNC_RSLAuth']:
 name='evidence/root0-weak-20261111/'+m+'.lean';old=subprocess.check_output(['git','show','HEAD:'+name]);s=old.decode()
 if m=='NNC_RSLReads':
  for x in ['read0','read6']:
   oldline='exact ofExcept_return _ _ _ _ '+x;assert s.count(oldline)==1;s=s.replace(oldline,'exact RSL.TASRev2.data_return _ _ _ _ '+x)
  s='import TAS_Rev2Support\n'+s
 else:
  oldline='   unfold mapVErr at mapped\n';assert s.count(oldline)==1;s=s.replace(oldline,oldline+'   obtain ⟨_,_,_,_,mapped,_⟩ := rsbind_return _ _ _ _ _ mapped\n')
 rows.append(dict(module=m,path=name,old_sha256=H(old),new_sha256=H(s.encode()),recipe='TAS_G0_BRIEF section5 replacement, strict match',new_source_replayed_by_NNI=False,selected_for_row_credit=False))
(E/'NNI_REPAIR_SOURCE_HASHES.json').write_text(json.dumps(dict(patch_sha256=H(patch.encode()),modules=rows,status='Expected repair hashes, not replay credit; no dependent344/240/top term is credited'),indent=1)+'\n')
p=E/'NNI_SPECIFICATION.json';x=json.loads(p.read_text());x['merged_module_repairs']['source_hashes']=rows;p.write_text(json.dumps(x,indent=1)+'\n');print('Five before/after source hashes recorded, no foreign file edited')
