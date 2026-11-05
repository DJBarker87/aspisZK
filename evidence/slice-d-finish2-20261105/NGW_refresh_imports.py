from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
catalog_file=E/'NGW_EXPECTED_IMPORTS.jsonl'
catalog={row['module']:row for line in catalog_file.read_text().splitlines()for row in[json.loads(line)]}
sources=list(E.glob('NGW*.lean'))
for directory in ['NGW_HelperRef']:
 if (E/directory).exists():sources+=list((E/directory).glob('*.lean'))
for source in sources:
 text=source.read_text();assert not text.startswith('{'),source
 name=source.stem if source.parent==E else source.parent.name+'.'+source.stem
 imports=['Init']+[word for line in text.splitlines()if line.startswith('import ')for word in line[7:].split()if word!='all']
 catalog[name]=dict(module=name,imports=list(dict.fromkeys(imports)),source_path=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
catalog_file.write_text(''.join(json.dumps(catalog[name])+'\n'for name in sorted(catalog)))
print(json.dumps(dict(own_source_baselines=len(sources),total=len(catalog))))
