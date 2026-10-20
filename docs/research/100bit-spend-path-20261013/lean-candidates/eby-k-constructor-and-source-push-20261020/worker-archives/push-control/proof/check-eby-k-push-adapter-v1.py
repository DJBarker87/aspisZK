from pathlib import Path
import argparse, hashlib, json, re, textwrap
p=argparse.ArgumentParser();p.add_argument('generated');p.add_argument('adapter');a=p.parse_args()
gen=Path(a.generated).read_text();ad=Path(a.adapter).read_text()
def decl(s, marker, next_marker):
    i=s.index(marker); j=s.index(next_marker,i)
    return s[i:j]
raw=decl(gen,'def fast_pairing.EbyKDot.push\n','/-- [eby_k_push_cut::push_entry]:')
adapt=decl(ad,'def pushWithOps\n','theorem result_bind_ok_inv')
def body(d):
    m=re.search(r':= do\n(.*)',d,re.S)
    assert m
    return textwrap.dedent(m.group(1)).strip()
r=body(raw)
subs=[('fast_pairing.canonical.Q.from_wide','fromWide'),
      ('fast_pairing.checked_q','checkedQ'),
      ('fast_pairing.canonical.Dot.push','pushDot'),
      ('self.count + 1#usize','addUsize self.count 1#usize'),
      ('fast_pairing.MAX_TERMS','maxTerms')]
counts={}
for old,new in subs:
    counts[old]=r.count(old)
    r=r.replace(old,new)
assert counts=={'fast_pairing.canonical.Q.from_wide':1,'fast_pairing.checked_q':1,'fast_pairing.canonical.Dot.push':2,'self.count + 1#usize':1,'fast_pairing.MAX_TERMS':1},counts
assert r==body(adapt), (r,body(adapt))
assert 'FunsExternal' not in ad and 'FunsExternal_Template' not in ad
assert not re.search(r'set_option\s+max(Heartbeats|RecDepth)',ad)
print(json.dumps({'ok':True,'substitution_counts':counts,
 'generated_sha256':hashlib.sha256(Path(a.generated).read_bytes()).hexdigest(),
 'adapter_sha256':hashlib.sha256(Path(a.adapter).read_bytes()).hexdigest(),
 'normalized_body_sha256':hashlib.sha256(r.encode()).hexdigest()},indent=2))
