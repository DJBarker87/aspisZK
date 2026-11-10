# usage: bash runl.sh PCWE_L001 PRVEq_X
cd "$(dirname "$0")"
python3 PCWE_run.py "$1" lean "$2" > "$1.client.log" 2>&1
echo "exit $?" >> "$1.client.log"
