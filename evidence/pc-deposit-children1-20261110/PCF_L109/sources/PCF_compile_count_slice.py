from pathlib import Path
import subprocess,json,time,hashlib,re
B=Path.cwd();cfg=json.loads((B/'PCF_L109.json').read_text());rows=[]
for mod in ['PCF_CountSliceRef.Types','PCF_CountSliceRef.Funs']:
 src=B/'PCF_generated'/(mod.replace('.','/')+'.lean');out=B/'PCF_objects'/(mod.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 log=B/(mod+'.time');cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','PCF_generated','-o',str(out),str(src)]
 start=time.monotonic();r=subprocess.run(['/usr/bin/time','-v','-o',str(log),*cmd]);s=log.read_text();row=dict(target=mod,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=re.search(r'Maximum resident set size.*?: (\d+)',s).group(1),swaps=re.search(r'Swaps: (\d+)',s).group(1),source_revision=cfg['source_revision'],source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),print_axioms='N/A: generated definitions only; all reference theorem roots audited separately',limits=cfg.get('limits','Inherited outer6G/8G/0swap/64tasks scope'))
 rows.append(row);(B/'PCF_COUNT_SLICE_COMPILE.json').write_text(json.dumps(rows,indent=1)+'\n')
 if r.returncode:raise SystemExit(r.returncode)
print('PCF generated count slice Types then Funs compiled serially; per-target resources recorded')
