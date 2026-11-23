"""Verify pinned original Git objects, cited line spans and the previous study's adapter."""
import argparse
from hashlib import sha1, sha256
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent


def check(source, repository):
    mapping = json.loads((HERE / 'source_map.json').read_bytes())
    imports = json.loads((HERE / 'imports.json').read_bytes())
    pins = {f"src/{name.replace('.', '/')}.lean": row['git_blob'] for name, row in imports.items()}
    for row in mapping['original']:
        data = (source / row['path']).read_bytes()
        lines = data.splitlines(keepends=True)
        assert 1 <= row['start'] <= row['end'] <= len(lines)
        chunk = b''.join(lines[row['start'] - 1:row['end']])
        assert sha256(data).hexdigest() == row['sha256']
        assert sha256(chunk).hexdigest() == row['span_sha256']
        pins[row['path']] = row['git_blob']
    for path, oid in pins.items():
        raw = (source / path).read_bytes()
        assert sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == oid
    prior = mapping['prior']
    body = (HERE / 'FieldEndpoints.lean').read_bytes()
    assert sha256(body).hexdigest() == prior['sha256']
    assert sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest() == prior['git_blob']
    if repository:
        args = ['git', '-C', repository, 'ls-tree', '-r', '-z', mapping['pin'], '--', *pins]
        records = subprocess.check_output(args).rstrip(b'\0').split(b'\0')
        checked = {}
        for item in records:
            header, path = item.split(b'\t', 1)
            checked[path.decode()] = header.split()[2].decode()
        assert checked == pins
        oid = subprocess.check_output(['git', '-C', repository, 'rev-parse',
                                       prior['commit'] + ':' + prior['path']], text=True).strip()
        assert oid == prior['git_blob']
    return {'commit': mapping['pin'], 'closure_modules': len(imports), 'cited_spans':len(mapping['original']),
            'distinct_original_files': len(pins), 'previous_adapter': prior['commit'], 'git_trees_checked': bool(repository)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--git', type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.source, args.git), indent=2))
