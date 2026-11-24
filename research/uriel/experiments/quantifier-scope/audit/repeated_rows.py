"""Post hoc paired views of the same printed circuit row under two survivor selections."""
from collections import defaultdict
import argparse
import csv
from fractions import Fraction
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads((ROOT / path).read_bytes())


def paired_views():
    cases = read('circuits/records.json')
    with (ROOT / 'pilot/results/cases.csv').open() as stream:
        scored = {c['record']: c for c in csv.DictReader(stream)}
    occurrences = defaultdict(list)
    for name, case in sorted(cases.items()):
        folder = Path('pilot/observed') / name / 'labels'
        prefix = read(folder / 'request.json')['messages'][-1]['content'].splitlines()
        answer = read(folder / 'response.json')['answer']
        for position, sid in enumerate(case['survivors']):
            text, = [line for line in prefix if line.startswith(sid + ' ')]
            row = case['states'][sid]
            label = 'Y' if Fraction(row['target_current']) > Fraction(case['target_threshold']) else 'N'
            assert label == text.split()[-1]
            occurrences[(case['family'],sid)].append(dict(
                record=name, position=position + 1, partner=case['survivors'][1-position],
                sentence=text, physical_label=label, report=None if answer is None else answer[sid],
                pattern=scored[name]['pattern'], expected=scored[name]['any_truth'] + scored[name]['both_truth'],
                response=scored[name]['response_pair']))
    output = []
    for (family,sid), views in sorted(occurrences.items()):
        assert len(views) == 2 and len({v['partner'] for v in views}) == 2
        assert views[0]['sentence'] == views[1]['sentence']
        assert views[0]['physical_label'] == views[1]['physical_label']
        label = views[0]['physical_label']
        output.append(dict(family=family, id=sid, label=label, views=views,
                           matching=sum(v['report'] == label for v in views),
                           delivered=sum(v['report'] is not None for v in views)))
    assert len(output) == 24
    return dict(analysis='Post hoc same-row comparison', unique_printed_rows=len(output),
                row_transcriptions=sum(len(v['views']) for v in output), rows=output)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=paired_views()
    archive=ROOT / 'audit/repeated_rows.json'
    content=json.dumps(result,indent=2)+'\n'
    if args.write:
        archive.write_text(content)
    elif content!=archive.read_text():
        raise ValueError('Repeated-row comparison differs')
    print(f'{len(result["rows"])} identical printed rows each seen twice.')
    for row in result['rows']:
        if row['matching']!=2:
            print(row['family'],row['id'],row['label'],[(v['record'],v['report']) for v in row['views']])
