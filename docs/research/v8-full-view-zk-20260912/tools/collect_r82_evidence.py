#!/usr/bin/env python3
"""Reuse the public-only R81 collector on the four pinned follow-up stages."""
from pathlib import Path
source=Path(__file__).with_name('collect_r81_evidence.py').read_text()
source=source.replace("control=base/'aspis-r20-r69-explicit-20260929-b'","control=base/'aspis-r20-r81-scalarg-20260929-a'")
source=source.replace("variants=['square','shortdot','semantic','powerbasis','shortinline','compose','privatebasis','scalarg']","variants=['pair','inline','affine','compose','unroll','dotinline','matrix']")
source=source.replace("len(pm['files'])==202","len(pm['files'])==210")
source=source.replace('6a8d46585bcebaeca27fbb88c936e2379ce45f3f314a01f7d37d7b995bb8e8ab','befe62a23b9ad254a82ac068ee277790e48c172a12acb324fc0555ab075c6263')
source=source.replace("f'aspis-r20-r81-{variant}-20260929-a'","f'aspis-r20-r82-{variant}-20260929-a'")
source=source.replace("    copy(control/'full-trace'/n,out/'control/full-trace'/n)","    if (control/'full-trace'/n).exists():copy(control/'full-trace'/n,out/'control/full-trace'/n)")
source=source.replace("'control_source_pins':202","'control_source_pins':210")
source=source.replace('4b64f97254e18f0338e1ad6229ca8407143aeb2b','9e0f3964610e74284510d81066971b339c124bdd')
exec(compile(source,str(Path(__file__).with_name('collect_r81_evidence.py')),'exec'))
