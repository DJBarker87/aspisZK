#!/usr/bin/env python3
"""Check pinned source bytes and the explicitly selected unchanged Rust items."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
manifest=json.loads((E/'s6-native-parent-total-source-pins.json').read_text())
sha=lambda text:hashlib.sha256(text.encode()).hexdigest()
def functions(text,name):
    found=[]
    pattern=r'(?m)^[ \t]*(?:pub(?:\([^)]*\))?\s+)?fn\s+'+re.escape(name)+r'\s*(?:[<(])'
    for match in re.finditer(pattern,text):
        start=match.start();i=text.index('{',match.end());depth=0
        while i<len(text):
            if text.startswith('//',i):
                i=text.find('\n',i);continue
            if text.startswith('/*',i):
                nested=1;i+=2
                while nested:
                    if text.startswith('/*',i):nested+=1;i+=2
                    elif text.startswith('*/',i):nested-=1;i+=2
                    else:i+=1
                continue
            if text[i]=='"':
                i+=1
                while text[i]!='"':i+=2 if text[i]=='\\' else 1
                i+=1;continue
            if text[i]=='{':depth+=1
            if text[i]=='}':
                depth-=1
                if depth==0:found.append(text[start:i+1]);break
            i+=1
    return found
for file,row in manifest['relevant_rust_source_comparison'].items():
    texts={rev:subprocess.check_output(['git','show',rev+':'+file],cwd=R,text=True) for rev in row['file_sha256']}
    assert all(sha(text)==row['file_sha256'][rev] for rev,text in texts.items()),file
    if row['byte_equal']:
        assert len(set(row['file_sha256'].values()))==1,file
    else:
        for name,expected in row.get('byte_equal_relevant_function_spans',{}).items():
            assert all([sha(s) for s in functions(text,name)]==expected for text in texts.values()),(file,name)
        for name,expected in row.get('byte_equal_relevant_constant',{}).items():
            pattern=r'(?m)^[ \t]*(?:pub(?:\([^)]*\))?\s+)?const\s+'+name+r'\b[\s\S]*?;[ \t]*(?:\n|$)'
            assert all(sha(re.search(pattern,text)[0])==expected for text in texts.values()),(file,name)
        diff=subprocess.check_output(['git','diff','--unified=0',manifest['original_native_extraction_revision'],manifest['historical_freeze'],'--',file],cwd=R,text=True)
        hunks=re.findall(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',diff,re.M)
        assert hunks and all((int(count) if count else 1)==0 for _,count,_,_ in hunks),file
print(json.dumps({'relevant_files':len(manifest['relevant_rust_source_comparison']),'whole_file_or_explicit_item_comparison':True,'compiled_release_binding':False}))
