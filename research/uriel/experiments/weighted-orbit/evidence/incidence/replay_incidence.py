"""Freshly compile the original window definition and replay the incidence supplement."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def run(command, cwd, env):
    return subprocess.check_output(command, env=env, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def main():
    args = argparse.ArgumentParser(description=__doc__)
    for field in ("checkout", "original", "toolchain", "mathlib"):
        args.add_argument("--" + field, required=True, type=lambda s: Path(s).resolve())
    cfg = args.parse_args()
    sys.path.insert(0, str(cfg.checkout / "research/uriel/experiments/joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative
    env, version = environment(cfg.toolchain, cfg.mathlib)
    direct = "Formalism.SubspaceCounting.StatementB"
    supplement = "WindowIncidence"
    source = Path(__file__).with_name(supplement + ".lean").read_bytes()
    digest = sha256(source).hexdigest()
    if digest != "678685c984506291d6e47094f597a7a39d01d14e145b93fad294407d97b0ae2d":
        raise ValueError("The proof source differs from the version reported.")
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        graph = closure([direct], cfg.original, pinned_tree(), dest=work)
        if graph != {direct: []}:
            raise ValueError("Unexpected original module closure")
        env["LEAN_PATH"] = str(work) + os.pathsep + env["LEAN_PATH"]
        original_path = relative(direct, ".lean")
        (work / (supplement + ".lean")).write_bytes(source)
        logs = {}
        for module in (direct, supplement):
            file = relative(module, ".lean")
            log = run([cfg.toolchain/"bin/lean", *FLAGS, "--root=.", "-o", file.with_suffix(".olean"), file], work, env)
            checked = run([cfg.toolchain/"bin/leanchecker", "-v", module], work, env)
            if checked != "replaying " + module:
                raise ValueError(checked)
            logs[module] = {"compilation": log, "kernel": checked}
        expected = {f"'OrbitIncidence.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for name in ("containing_starts", "total_window_occupancy", "cap_necessary")}
        if logs[direct]["compilation"] or set(logs[supplement]["compilation"].splitlines()) != expected:
            raise ValueError(logs)
        print(json.dumps({"original_pin": PIN, "original_git_blob": pinned_tree()["src/" + str(original_path)],
                          "original_source_sha256": sha256((work/original_path).read_bytes()).hexdigest(),
                          "supplement_sha256": digest, "toolchain": version, "flags": FLAGS,
                          "modules": logs}, indent=2))


if __name__ == "__main__":
    main()
