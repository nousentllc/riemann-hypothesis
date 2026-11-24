"""Check the carried-forward registry and seven historical answers against parent Git objects."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PARENT = 'e7a01b2d19e61e77b97ece9f1b48d48bb761e186'
PREFIX = 'research/uriel/experiments/label-first-verdict/'
ROOT = Path(__file__).resolve().parents[1]


def read_local(relative_path):
    return json.loads((ROOT / relative_path).read_bytes())


def audit(repository):
    anchors = {}

    def fetch(path):
        ref = PARENT + ':' + PREFIX + path
        content = subprocess.check_output(['git', '-C', repository, 'cat-file', 'blob', ref])
        oid = subprocess.check_output(['git', '-C', repository, 'rev-parse', ref], text=True).strip()
        blob = b'blob ' + str(len(content)).encode() + b'\0' + content
        assert hashlib.sha1(blob).hexdigest() == oid
        anchors[path] = dict(git_blob=oid, sha256=hashlib.sha256(content).hexdigest())
        return json.loads(content)

    historical_ids = fetch('circuits/historical_ids.json')
    seen_ids = {k: set(v) for k, v in historical_ids.items()}
    for row in fetch('circuits/records.json').values():
        family = row['family'].removeprefix('DC-')
        ids = set(row['states'])
        assert family not in historical_ids
        assert seen_ids.setdefault(family, ids) == ids
    assert seen_ids == {k: set(v) for k, v in read_local('circuits/historical_ids.json').items()}
    prior = fetch('circuits/verification.json')
    footprints = dict(prior['previous_graph_sizes'], **prior['new_graph_sizes'])
    current = read_local('circuits/verification.json')
    assert footprints == current['previous_graph_sizes']
    assert not {tuple(x) for x in footprints.values()} & {tuple(x) for x in current['new_graph_sizes'].values()}
    selected = read_local('audit/historical_seven.json')
    assert selected['commit'] == PARENT and len(selected['cases']) == 7
    for record, case in selected['cases'].items():
        for stage, key in [('labels', 'checkpoint'), ('verdict', 'final')]:
            path = f'pilot/observed/{record}_label_first/{stage}/response.json'
            receipt = fetch(path)
            assert case[key + '_source'].endswith('/' + PARENT + '/' + PREFIX + path)
            assert case[key + '_sha256'] == anchors[path]['sha256']
            assert case[key + '_text'] == receipt['content']
    return dict(parent_commit=PARENT, parent_directory=PREFIX,
                historical_layouts=len(seen_ids), historical_ids=len(set.union(*seen_ids.values())),
                historical_label_verdict_pairs=len(selected['cases']), parent_blobs=anchors)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path, help='Local Git repository containing the pinned experiment parent')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = audit(args.repository)
    content = json.dumps(data, indent=2, sort_keys=True) + '\n'
    path = ROOT / 'audit/parent_anchors.json'
    if args.write:
        path.write_text(content)
    elif path.read_text() != content:
        raise ValueError('Archived parent-object report differs')
    print(f'Checked {len(data["parent_blobs"])} parent blobs, {data["historical_layouts"]} layouts, '
          f'{data["historical_ids"]} row IDs and {data["historical_label_verdict_pairs"]} historical verdicts.')
