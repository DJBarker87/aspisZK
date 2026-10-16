#!/usr/bin/env python3
"""Hash the actual current parser declarations against accepted extraction pins."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
HERE=Path(__file__).resolve().parent
ROOT=Path(subprocess.check_output(['git','-C',str(HERE),'rev-parse','--show-toplevel'],text=True).strip())
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
sha=lambda b:hashlib.sha256(b).hexdigest()
def build():
 utility=BASE/'tools/public-serializer-extraction-kit/extract.py'
 spec=importlib.util.spec_from_file_location('cutter',utility);c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
 pins=json.loads((BASE/'tools/prefix-aggregate-extraction-kit/source-pins.json').read_text())
 source=ROOT/'crates/aspis-r1-cost-probe/src/r1_wire.rs'
 anchors={'wire_error':'pub enum Error {','prefix_type':'pub struct Prefix','prefix_parse':"pub fn parse(bytes: &'a [u8])"}
 rows=[]
 for name,anchor in anchors.items():
  old=next(x for x in pins['declaration_cuts'] if x['name']==name)
  text,start,end,first,last=c.find_item(source,anchor)
  assert sha(text)==old['sha256'],name
  rows.append({'declaration':name,'current_source_sha256':sha(text),'accepted_source_sha256':old['sha256'],'classification':'unchanged','current_start_byte':start,'current_end_byte_exclusive':end,'source_statement_diff':''})
 return {'scope':'Source bodies needed by the concrete Prefix/Error nominal adapter. The adapter is not an equality theorem about an un-emitted current Prefix.parse constant. Its actual parser body is the unchanged accepted source cut.','source_path':str(source.relative_to(ROOT)),'source_revision':'69da71ea36d4dd511ecfe3204b33c54555d18ca4','declarations':rows}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();b=(json.dumps(build(),indent=2)+'\n').encode();p=HERE/'source-audit.json'
 if a.check:assert p.read_bytes()==b
 else:p.write_bytes(b)
 print(json.dumps({'status':'PASS','declarations':3,'audit_sha256':sha(b),'checked':a.check}))
if __name__=='__main__':main()
