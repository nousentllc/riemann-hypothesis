"""Rebuild the distribution ZIP from the checksummed extracted package."""
import argparse
from hashlib import sha256
from io import BytesIO
from pathlib import Path
import re
import zipfile


def archive(root_name, entries):
    stream = BytesIO()
    with zipfile.ZipFile(stream, "w") as output:
        for name in sorted(entries):
            member = zipfile.ZipInfo(root_name + "/" + name, (2026, 11, 23, 0, 0, 0))
            member.create_system = 3
            member.external_attr = 0o100644 << 16
            output.writestr(member, entries[name], compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    return stream.getvalue()


def verify(root, entries):
    manifest = entries["SHA256SUMS"].decode().splitlines()
    names = set()
    for line in manifest:
        match = re.fullmatch(r"([a-f0-9]{64})  (.+)", line)
        if not match:
            raise ValueError("Invalid checksum row")
        digest, name = match.groups()
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or name in names or name == "SHA256SUMS":
            raise ValueError("Invalid repeated or unsafe manifest path: " + name)
        if name not in entries or sha256(entries[name]).hexdigest() != digest:
            raise ValueError("Checksum mismatch: " + name)
        names.add(name)
    if names != set(entries) - {"SHA256SUMS"}:
        raise ValueError("The package directory has files absent from its manifest")
    return archive(root.name, entries)


def main():
    arg = argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--directory", type=Path, default=Path(__file__).resolve().parents[1])
    arg.add_argument("--output", type=Path, required=True)
    opts = arg.parse_args()
    root = opts.directory.resolve(strict=True)
    target = opts.output.resolve()
    if root == target or root in target.parents:
        arg.error("Choose an output path outside the package")
    entries = {p.relative_to(root).as_posix():p.read_bytes() for p in root.rglob("*") if p.is_file()}
    contents = verify(root, entries)
    target.write_bytes(contents)
    print(sha256(contents).hexdigest(), target)


if __name__ == "__main__":
    main()
