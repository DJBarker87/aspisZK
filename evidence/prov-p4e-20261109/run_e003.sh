cd "$(dirname "$0")"
python3 PCWE_run.py PCWE_E003 refextract > PCWE_E003.client.log 2>&1
echo "exit $?" >> PCWE_E003.client.log
