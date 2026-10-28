"""Check the exact retained deployed Zeroizing delegation and reached call."""
from pathlib import Path
import subprocess,re,hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';p=E/'native-61307/zeroize-1.9.0-lib.rs.txt';b=p.read_bytes();s=b.decode()
body=re.search(r'impl<Z> Zeroize for Zeroizing<Z>\s*where\s*Z: Zeroize \+ \?Sized,\s*\{\s*fn zeroize\(&mut self\) \{(?P<body>.*?)\}\s*\}',s,re.S)
assert body and re.sub(r'\s+','',body['body'])=='self.0.zeroize();'
q='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_W_R_ReserveBuild.lean';actual=subprocess.check_output(['git','show','HEAD:'+q]);assert actual.count('let _ ← invoke "zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize"'.encode())==1
corrected=json.loads((E/'native-61311/result.json').read_text())['sources']['lib.rs']['sha256']
assert hashlib.sha256(b).hexdigest()==corrected
controls=[]
for tag,changed in [('omitted',''),('duplicated','self.0.zeroize(); self.0.zeroize();'),('other','self.0.zeroize(); unreachable!();')]:
 tamper=s[:body.start('body')]+changed+s[body.end('body'):]
 x=body.re.search(tamper);valid=bool(x and re.sub(r'\s+','',x['body'])=='self.0.zeroize();');assert not valid;controls.append(dict(name=tag,rejected=True))
(E/'wrapper-source-binding.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(b).hexdigest(),corrected_61311_source_sha256=corrected,matches_corrected_deployed_resolution_source=True,source_capture=str(p.relative_to(R)),body=body[0],reached_source=q,reached_sha256=hashlib.sha256(actual).hexdigest(),controls=controls,evidence_class='structural delegation check; primitive byte effect law inherited from restored V221/V222; not whole native runtime'),indent=2)+'\n')
