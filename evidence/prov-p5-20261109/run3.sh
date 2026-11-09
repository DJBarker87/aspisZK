#!/bin/bash
# usage: run3.sh ATTEMPT BUNDLE
python3 -B PCT_run.py "$1" lean "$2" 2>&1 | tail -1 | python3 -c "
import sys,json
d=json.loads(sys.stdin.read());print({k:v for k,v in d.items() if k!='print_axioms'},len(d['print_axioms']))"
xz -dc "$1/stdout.log.xz" > "gen/$1.log"
