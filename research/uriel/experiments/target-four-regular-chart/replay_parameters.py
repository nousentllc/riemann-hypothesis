"""Standalone readable-toolchain replay of the parameter rectangle identities."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile

from replay import module, write_result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk",type=Path,required=True)
    parser.add_argument("--mathlib",type=Path,required=True)
    parser.add_argument("--receipt",type=Path)
    a=parser.parse_args()
    sdk,lib=a.sdk.resolve(),a.mathlib.resolve()
    ver=subprocess.check_output([sdk/"bin/lean","--version"],text=True).strip()
    pin=subprocess.check_output(["git","-C",lib,"rev-parse","HEAD"],text=True).strip()
    if "4.35.0," not in ver or pin!="56a005855ea17e0b0958f73ec801ae140b0a1679":
        raise ValueError("Unexpected compiler or Mathlib")
    with tempfile.TemporaryDirectory() as tmp:
        work=Path(tmp)
        paths=[work,lib/".lake/build/lib/lean",*sorted((lib/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]
        # The readable checkout installs Mathlib's sibling packages alongside Mathlib.
        paths.extend(sorted(lib.parent.glob("*/.lake/build/lib/lean")))
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,paths)))
        row=module(sdk,"ReadableBoxParameters",work,env)
        write_result(dict(compiler=ver,mathlib=pin,modules=[row]),a.receipt)


if __name__=="__main__":
    main()
