import pathlib,json,hashlib,ast
H=pathlib.Path(__file__).resolve().parent
p=H/'remote.py'; s=p.read_text()
v=json.loads((H.parent/'inventory.json').read_text()); root=v['toolchain']['source_root']
paths={str(pathlib.Path(root)/x['source_path'].removeprefix('core/src/')):x['sha256'] for x in v['source_files']}
s=s.replace("    actual={k:sha(v) for k,v in paths.items()}","    std_expected="+repr(paths)+"\n    std_before={k:sha(pathlib.Path(k)) for k in std_expected}\n    assert std_before==std_expected\n    actual={k:sha(v) for k,v in paths.items()}")
s=s.replace("    baseline_after=sha(baseline)","    baseline_after=sha(baseline)\n    std_after={k:sha(pathlib.Path(k)) for k in std_expected}\n    assert std_after==std_expected")
s=s.replace("'source_hashes_before':actual,", "'stdlib_hashes_before':std_before,'source_hashes_before':actual,")
s=s.replace("'source_hashes_after':source_after,", "'stdlib_hashes_after':std_after,'source_hashes_after':source_after,")
s=s.replace('observer_stdout','charon_stdout').replace('observer_stderr','charon_stderr')
s=s.replace("'frame_marker_counts':{k:root.joinpath('charon.stderr.log').read_text(errors='replace').count(k) for k in ['ASPIS_R427_RAW_MIR_BEGIN','ASPIS_R427_RAW_MIR_END','ASPIS_R427_STATEMENT_SOURCE','ASPIS_R427_USE_RETAG','ASPIS_R427_TERMINATOR_SOURCE','ASPIS_R427_CALL_ARG']},",'')
ast.parse(s); p.write_text(s)
print(hashlib.sha256(s.encode()).hexdigest())
