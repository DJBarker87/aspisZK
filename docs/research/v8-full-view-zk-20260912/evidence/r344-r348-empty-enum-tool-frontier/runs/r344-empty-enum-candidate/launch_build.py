import pathlib,subprocess,shlex,json,hashlib
here=pathlib.Path(__file__).resolve().parent
runner=here/'run_cached_build.py';rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
(here/'history').mkdir(exist_ok=True);(here/'history/run_cached_build-prelaunch.py').write_bytes(runner.read_bytes());runner.write_text(runner.read_text().replace('2e1ece93ae5834f2586ae5f6f75cd0f9856ab801',rev).replace("print('R312_BUILD_EXIT'","print('R344_BUILD_EXIT'"))
remote='/home/dombarker/project-offloads/aspis-r344-direct-empty-enum-candidate-20261002-a'
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
subprocess.run(['scp',*opts,str(runner),host+':'+remote+'/candidate-audit/run_cached_build.py'],check=True)
argv=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r344-direct-empty-enum-build','--working-directory='+remote+'/src','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3',remote+'/candidate-audit/run_cached_build.py']
(here/'lead-launch.json').write_text(json.dumps({'source_revision':rev,'runner_sha256':hashlib.sha256(runner.read_bytes()).hexdigest(),'argv':argv,'lead_review':'Exact one-file direct-empty-enum candidate inspected. Only impossible typed variants removed; original retained variants/source rows and multi-inhabited guard unchanged. Parent/source/cache inode audit passed; focused cached release build only, compiler correspondence remains unproved.','expected_step':'Cached InterpExpansion native compilation and relink, not proof generation or benchmarks.','measurement_boundary':'Compiler GNU time and sampled actual container cgroup; Docker CLI RSS is not aggregate compiler RSS.'},indent=2)+'\n')
with (here/'build-launch.log').open('w') as out:r=subprocess.run(['ssh',*opts,host,shlex.join(argv)],stdout=out,stderr=subprocess.STDOUT)
print((here/'build-launch.log').read_text());subprocess.run(['scp','-r',*opts,host+':'+remote+'/candidate-audit',str(here)],check=True);raise SystemExit(r.returncode)
