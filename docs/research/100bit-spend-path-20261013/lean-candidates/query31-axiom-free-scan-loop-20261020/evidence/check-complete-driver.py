from pathlib import Path
import re,json,hashlib,sys
p=Path(sys.argv[1]);raw=(p/'source-snapshot/generated/AspisR1Query31Transcript/Funs.lean').read_text();ours=(p/'sources/Query31UnrolledDriverFirstStop.lean').read_text()
def decl(s,name):
 s=re.sub(r'(?m)^@\[[^\n]*\]\s*\n','',s)
 m=re.search(r'(?m)^def\s+'+re.escape(name)+r'(?=\s|:|\n)',s);assert m,name
 tail=s[m.end():];n=re.search(r'(?m)^(?:(?:private\s+)?(?:def|theorem|lemma|inductive|structure)|end)\b|^/--',tail)
 return s[m.start():m.end()+n.start()] if n else s[m.start():]
def compact(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'(?m)^\s*--.*$','',s);return re.sub(r'\s+',' ',s).strip()
results={}
for name in ['aspis_core.r0_transcript.QUERY_COUNT','aspis_core.r0_transcript.QUERY_MAX_DRAWS','aspis_core.r0_transcript.QueryScan.finish']:
 a,b=compact(decl(raw,name)),compact(decl(ours,name));assert a==b,(name,a,b);results[name]={'exact':True,'normalized_sha256':hashlib.sha256(a.encode()).hexdigest()}
a=decl(raw,'aspis_core.r0_transcript.queries_from_pairs').split(':= do',1)[1]
b=decl(ours,'queries_from_pairs_with_scan').split(':= do',1)[1]
a,n=re.subn(r'let scan ←\s*aspis_core\.r0_transcript\.QueryScan\.Insts\.CoreDefaultDefault\.default','let scan := scan0',a);assert n==1
# Every entire scan call keeps its state/block arguments and ordering.
a,n=re.subn(r'aspis_core\.r0_transcript\.QueryScan\.scan(?=\s)', 'scanFn',a);assert n==8
assert compact(a)==compact(b),(compact(a)[-350:],compact(b)[-350:])
results['queries_from_pairs']={'complete_body_equal':True,'default_boundary_substitutions':1,'scan_boundary_substitutions':8,'normalized_sha256':hashlib.sha256(compact(a).encode()).hexdigest()}
print(json.dumps({'pass':True,'scope':'exact emitted unrolled CANDIDATE body; default and scan are explicit operations, original iterator equivalence/adoption OPEN','declarations':results},indent=2))
