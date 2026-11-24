"""Build the two-reading records from six exact circuit layouts."""
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
from string import ascii_uppercase

# Allow both direct execution and importlib loading in the common study runner.
if __package__:
    from .network import NETWORKS, all_states, network_edges
else:
    import importlib.util
    _spec = importlib.util.spec_from_file_location(
        "proof_audit_dc_network", Path(__file__).with_name("network.py"))
    _network = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_network)
    NETWORKS, all_states, network_edges = _network.NETWORKS, _network.all_states, _network.network_edges

HERE = Path(__file__).resolve().parent


def scrambled(values, salt):
    def order(value):
        return sha256((salt + ":" + value).encode()).digest()
    return sorted(values, key=order)


def row_ids():
    pool = ["".join(pair) for pair in product(ascii_uppercase, repeat=2)]
    historical_ids = set(scrambled(pool, "net-ref-2026")[:64])
    labels = scrambled([q for q in pool if q not in historical_ids], "threshold-bits-20261124")
    return {key:labels[i*8:i*8+8] for i,key in enumerate(sorted(NETWORKS))}


def description(probe):
    variable, cutoff = probe
    if variable.startswith("I"):
        return f"signed current of R{variable[1:]} > {cutoff} A"
    return f"voltage at {variable[1:]} > {cutoff} V"


def signal(readings, probe):
    variable, threshold = probe
    return "H" if readings[variable] > Fraction(threshold) else "L"


def packet_pair(key, design, ids):
    graph = network_edges(NETWORKS[key])
    settings = all_states(graph)
    labels = scrambled(["M2", "M3", "M4", "M5", "M6", "M7", "M8"], "meter:"+key)[:3]
    probes = dict(zip(labels, design["menu"]))
    menu = {label:description(probe) for label, probe in probes.items()}
    first = design["observed"]
    target = design["target"]
    states, initial_lamps, lines = {}, {}, {}
    for (bits, values), state_id in zip(settings,ids):
        obs = {label:signal(values,probe) for label,probe in probes.items()}
        states[state_id] = {"answer":signal(values,target)=="H", "obs":obs,
                            "bits":bits,"target_current":str(values[target[0]]),
                            "initial":signal(values,first)}
        initial_lamps[state_id] = signal(values, first)
        lines[state_id] = " ".join([state_id,bits,str(values[target[0]]),
                                    initial_lamps[state_id],*(obs[l] for l in labels)])
    resistors = []
    for i,(u,v,r,sw) in enumerate(graph,1):
        status = "" if sw=="-" else f"[{sw}]"
        resistors.append(f"R{i}={u}>{v}:{r}{status}")
    text = (
        "DC circuit at + = 12 V and 0 = 0 V. Three hidden switches s,t,u each have "
        "two positions (1 closed). A bracketed resistor conducts only with that "
        "switch closed. Edge format source>destination:ohms defines positive current. "
        + " ".join(resistors) + ".\n"
        + "Question: is the " + description(target) + "?\n"
        + "The calibration table lists all possible switch settings. Finite meter "
        "comparators report H for strictly above their threshold, L otherwise. "
        "All currents are exact amperes. Initial comparator: " + description(first)
        + ". Lookup comparators: " + "; ".join(k+" = "+v for k,v in menu.items()) + ".\n"
        + "ID stu target_current initial " + " ".join(labels) + "\n"
        + "\n".join(lines[i] for i in sorted(ids))
    )
    variants = []
    pair = [design["lookup_witness"],design["twin_witness"]]
    if not design["lookup_first"]:
        pair.reverse()
    for j,witness in enumerate(pair,1):
        actual = ids[witness]
        initial = initial_lamps[actual]
        variants.append({"family":"DC-"+key, "variant":str(j), "text":text,
                         "states":states, "eligible":sorted(i for i in ids if initial_lamps[i]==initial),
                         "actual":actual, "menu":menu, "domain":"circuits", "target_threshold":target[1],
                         "evidence":"The initial comparator reading is "+initial+"."})
    return variants


def build():
    design = json.loads((HERE/"design.json").read_text())
    identifiers = row_ids()
    records = {}
    for key, parameters in sorted(design.items()):
        for record in packet_pair(key, parameters, identifiers[key]):
            records[f"circuit-{len(records):02d}"] = record
    return records


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write deterministic records.json.")
    options = parser.parse_args()
    content = json.dumps(build(), indent=2, ensure_ascii=False) + "\n"
    target = HERE / "records.json"
    if options.write:
        target.write_text(content)
    elif target.read_text() != content:
        raise ValueError("Archived records differ from regenerated input")
    print(f"{len(build())} records")
