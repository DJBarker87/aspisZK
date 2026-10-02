import pathlib,json,hashlib
out=pathlib.Path(__file__).resolve().parent
root=out.parents[1]
src=root/'docs/research/v8-full-view-zk-20260912/evidence/r305-current-batch-reverse-raw/raw-adapter-audit/provenance/R292Funs.input.lean'
s=src.read_text(); assert hashlib.sha256(src.read_bytes()).hexdigest()=='4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4'
frags=[]
for a,b in [('        let i2 := Slice.len ys\n','        let s2 := alloc.vec.Vec.deref px2\n'),('        let s2 := alloc.vec.Vec.deref px2\n','        let i3 := Slice.len xs\n')]:
 assert s.count(a)==s.count(b)==1
 lo=s.index(a);hi=s.index(b,lo);frags.append(s[lo:hi])
header='''import Aeneas.Std
import AspisR318BatchPrefixRaw
import AspisR278PrivateInverseRaw
open Aeneas Aeneas.Std Result ControlFlow Error AspisR249R110Raw AspisR316SliceLastRaw AspisR318BatchPrefixRaw AspisR278PrivateInverseRaw

noncomputable section
namespace AspisR335PrefixPairInverseRaw

'''
target=out/'AspisR335PrefixPairInverseRaw.lean'
target.write_text(header+'def selectedPrefix1 (ys : Slice U32) : Result (alloc.vec.Vec U32) := do\n'+frags[0]+'        .ok py2\n\ndef selectedPairInverse (px2 py2 : alloc.vec.Vec U32) : Result (U32 × U32) := do\n'+frags[1]+'        .ok (ix, iy)\n\n#print axioms selectedPrefix1\n#print axioms selectedPairInverse\n\nend AspisR335PrefixPairInverseRaw\nend\n')
report={'scope':'Uncompiled exact source-contiguous second-prefix and shared-inverse fragments; full guards/setup/output excluded.','source_file':str(src.relative_to(root)),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'target_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'fragments':[{'text':f,'sha256':hashlib.sha256(f.encode()).hexdigest(),'source_line_start':s[:s.index(f)].count('\n')+1,'source_line_end':s[:s.index(f)+len(f)].count('\n'),'exact':target.read_text().count(f)==1} for f in frags],'operation_replacements':0,'harness_only':['imports/namespace/noncomputable','selectedPrefix1(ys) function wrapper and .ok py2','selectedPairInverse(px2,py2) function wrapper and .ok(ix,iy)','#print axioms'],'name_binding':'Existing R249 B type/mul, R318 exact forward loop1, R316 source Slice.last with its explicit checked-sub API adapter, R278 exact B.inv. Independent compiler/stdlib correspondence is not claimed.'}
(out/'raw-adapter.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
