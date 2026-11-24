"""Match every pinned original source link in README.md against the local Git object and archived hashes."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PIN = '40e56bab026552e089d7afcfeff08d2defb9c005'
URL = 'https://github.com/nousentllc/riemann-hypothesis/blob/' + PIN + '/'


def build_manifest(source, repo):
    ranges = {}
    for path, first, last in re.findall(re.escape(URL) + r'(src/[\w/]+\.lean)#L(\d+)-L(\d+)', (HERE / 'README.md').read_text()):
        ranges.setdefault(path, set()).add((int(first), int(last)))
    if not ranges:
        raise ValueError('No pinned source ranges.')
    files = {}
    for path, spans in sorted(ranges.items()):
        raw = (source / path).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        commit_blob = subprocess.check_output(['git', '-C', repo, 'rev-parse', PIN + ':' + path], text=True).strip()
        if blob != commit_blob:
            raise ValueError('File diverges from pinned original: ' + path)
        lines = raw.splitlines(keepends=True)
        selected = []
        for first, last in sorted(spans):
            if not 1 <= first <= last <= len(lines):
                raise ValueError(f'Bad range {path} {first}-{last}')
            selected.append(dict(first=first, last=last, sha256=hashlib.sha256(b''.join(lines[first - 1:last])).hexdigest()))
        files[path] = dict(git_blob=blob, sha256=hashlib.sha256(raw).hexdigest(), cited_ranges=selected)
    return dict(commit=PIN, files=files)


def transitive_scope(source, repo):
    """Count original project modules named in import headers using authenticated file bytes."""
    listing = subprocess.check_output(['git', '-C', repo, 'ls-tree', '-rz', PIN, '--', 'src'])
    files = {}
    for record in listing.split(b'\0'):
        if record:
            metadata, encoded_path = record.split(b'\t', 1)
            path = Path(encoded_path.decode())
            if path.suffix == '.lean':
                module = '.'.join(path.relative_to('src').with_suffix('').parts)
                files[module] = (path, metadata.split()[-1].decode())
    cache = {}

    def imports(module):
        if module not in cache:
            path, expected = files[module]
            raw = (source / path).read_bytes()
            digest = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            if digest != expected:
                raise ValueError('Unverified original: ' + str(path))
            headers = re.findall(r'(?m)^[ \t]*(?:(?:public|private)[ \t]+)?import[ \t]+([^\n]+)', raw.decode())
            names = [word for header in headers for word in header.split('--')[0].split()]
            cache[module] = {n for n in names if n in files}
        return cache[module]

    block = 'Development.AutomorphicSpectrum.Proofs.BlockDecomposition.'
    binary = 'Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.'
    roots = [block + n for n in ('CountingFormula', 'TestFunctionExists', 'LeftSideFormula', 'MeanValueFormula')]
    roots += [binary + 'SingleRowSide.Srside', binary + 'OneVecBinary']
    result = {}
    for root in roots:
        pending, visited = [root], set()
        while pending:
            module = pending.pop()
            if module not in visited:
                visited.add(module)
                pending.extend(imports(module) - visited)
        content = '\n'.join(sorted(visited)).encode() + b'\n'
        result[root] = dict(project_modules_including_root=len(visited), sorted_names_sha256=hashlib.sha256(content).hexdigest())
    return result


def validate_replay(receipt_path, reference_path):
    receipt = json.loads(receipt_path.read_text())
    if receipt['pin'] != PIN or receipt['mathlib'] != '0df444a360eaa60ab8c11dca51a86af692955474':
        raise ValueError('Wrong replay inputs')
    originals = set(receipt['source_files'])
    if len(originals) != 28 or set(receipt['original_modules']) != originals:
        raise ValueError('Original compilation list differs from source closure')
    if set(receipt['replays']) != originals | {'PositiveTestExtract'}:
        raise ValueError('Some compiled objects lack a separate kernel replay')
    for module, log in receipt['replays'].items():
        if 'replaying ' + module not in log.splitlines():
            raise ValueError('Missing replay line for ' + module)
    if len(receipt['axioms']) != 7 or any(set(a) - {'propext', 'Classical.choice', 'Quot.sound'} for a in receipt['axioms'].values()):
        raise ValueError('Unexpected axiom report')
    if reference_path:
        digest = hashlib.sha256(reference_path.read_bytes()).hexdigest()
        if digest != '375cbee2fc3fc0f5088ef2e6dc9a5ac5530924310dc62422ec65aac9dc4c1d25':
            raise ValueError('Unexpected published object manifest')
        references = {}
        for line in reference_path.read_text().splitlines():
            checksum, name = line.split(maxsplit=1)
            references[Path(name)] = checksum
        matches = set()
        for module, built in receipt['original_modules'].items():
            path = Path(*module.split('.')).with_suffix('.olean')
            match = references[path] == built['olean_sha256']
            if match != built['reference_match']:
                raise ValueError('Inconsistent hash comparison for ' + module)
            if match:
                matches.add(module)
        print(f'{len(matches)}/{len(originals)} original object digests match the published manifest.')
    print('Confirmed receipt structure, 29 logged module replays, and seven axiom reports.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--write', type=Path, help='Generate a manifest at this path instead of comparing with the archive.')
    parser.add_argument('--receipt', type=Path, help='Also validate a saved Lean replay receipt.')
    parser.add_argument('--reference', type=Path, help='Compare the receipt against original project object digests.')
    args = parser.parse_args()
    if args.receipt:
        validate_replay(args.receipt, args.reference)
    elif args.reference:
        parser.error('--reference requires --receipt')
    manifest = build_manifest(args.source, args.repo)
    manifest['project_import_header_closures'] = transitive_scope(args.source, args.repo)
    if args.write:
        args.write.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
    elif manifest != json.loads((HERE / 'source_manifest.json').read_text()):
        raise ValueError('Source manifest mismatch')
    count = sum(len(file['cited_ranges']) for file in manifest['files'].values())
    print(f'Authenticated {len(manifest["files"])} original files and {count} unique line ranges.')


if __name__ == '__main__':
    main()
