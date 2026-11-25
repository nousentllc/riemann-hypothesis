"""Fetch the selected public archives, check their hashes, and restore only these modules."""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent
ARTIFACTS = 'https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/'


def restore(sdk, directory, workers):
    entries = json.loads((ROOT / 'original_imports.json').read_text())
    archive_dir = directory / 'archives'
    archive_dir.mkdir(parents=True, exist_ok=True)

    def fetch(item):
        name, row = item
        archive = row['cache_archive']
        if not re.fullmatch(r'[0-9a-f]{16}\.ltar', archive) or not re.fullmatch(r"[\w']+(?:\.[\w']+)*", name):
            raise ValueError(name)
        dest = archive_dir / archive
        expected = row['archive_sha256']
        if not dest.exists() or hashlib.sha256(dest.read_bytes()).hexdigest() != expected:
            req = Request(ARTIFACTS + archive[:-5] + '.art', headers={'User-Agent': 'Nous-rank-one-study/1'})
            for attempt in range(3):
                try:
                    with urlopen(req, timeout=60) as response:
                        data = response.read()
                    if hashlib.sha256(data).hexdigest() != expected:
                        raise ValueError('Archive checksum differs for '+name)
                    dest.write_bytes(data)
                    break
                except OSError:
                    if attempt == 2:
                        raise
                    time.sleep(2**attempt)
        sub = Path(*name.split('.')).parent
        bases = [directory / 'obj' / sub, directory / 'ir' / sub]
        for base in bases:
            base.mkdir(parents=True, exist_ok=True)
        return dict(file=str(dest), hash=row['dep_hash'], base=list(map(str, bases)))

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        jobs = list(pool.map(fetch, entries.items()))
    subprocess.run([sdk/'bin/leantar','--jobs',str(workers),'-f','-x','-j','-'],
                   input=json.dumps(jobs), text=True, cwd=directory, check=True)
    for mod,row in entries.items():
        obj = directory/'obj'/Path(*mod.split('.')).with_suffix('.olean')
        if hashlib.sha256(obj.read_bytes()).hexdigest()!=row['used_olean_sha256']:
            raise ValueError('Restored object differs for '+mod)
    print(f'Verified {len(entries)} archives and unpacked objects in {directory/"obj"}')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk',type=Path,required=True)
    parser.add_argument('--destination',type=Path,required=True)
    parser.add_argument('--workers',type=int,default=6,choices=range(1,17))
    args=parser.parse_args()
    restore(args.sdk.resolve(),args.destination.resolve(),args.workers)
