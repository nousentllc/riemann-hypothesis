"""Post-hoc comparison with the published object manifest and a controlled package-name rebuild."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

from formal import FLAGS, PIN, dump, environment, original, sha

MANIFEST_SHA = "375cbee2fc3fc0f5088ef2e6dc9a5ac5530924310dc62422ec65aac9dc4c1d25"
URL = "https://math.mit.edu/~drew/grh/project-oleans.sha256"


def package_build(tc,env,work,scratch,module,output,tag,source_label=None):
    rel=Path(*module.split(".")).with_suffix(".lean")
    data=original("src/"+rel.as_posix())
    if (work/"src"/rel).read_bytes()!=data:
        raise ValueError(f"Source mismatch at {module}")
    setup={"name":module,"isModule":False,"importArts":{},"plugins":[],"dynlibs":[],"options":{}}
    if tag:
        setup["package"]=tag
    config=scratch/"setup.json"
    dump(config,setup)
    output.parent.mkdir(parents=True,exist_ok=True)
    args=[str(tc/"bin"/"lean"),*FLAGS,"--root=.",f"--setup={config}","-o",str(output)]
    args += ["--stdin",source_label] if source_label is not None else [str(rel)]
    proc=subprocess.run(args,input=(data if source_label is not None else None),env=env,cwd=work/"src",capture_output=True)
    messages=(proc.stdout+proc.stderr).decode()
    if proc.returncode or "declaration uses 'sorry'" in messages:
        raise ValueError(messages)
    return sha(output.read_bytes())


def source_label_controls(tc,env,work,out,published):
    path=out/"external_objects.json"
    record=json.loads(path.read_text())
    if record["pin"]!=PIN or record["manifest_sha256"]!=MANIFEST_SHA or record["tagged_endpoint_replay"]["exit"]!=0:
        raise ValueError("A completed verified package comparison is required")
    rows=record["tagged_build"]
    expected={r["module"] for r in json.loads((work/"prepared.json").read_text())["modules"]}
    if len(rows)!=len(expected) or {r["module"] for r in rows}!=expected:
        raise ValueError("Tagged comparison is missing project modules")
    rel=lambda row: Path(*row["module"].split(".")).with_suffix(".olean")
    prior=next((t for t in sorted(work.glob("tagged-oleans-*")) if all(
        (t/rel(r)).is_file() and sha((t/rel(r)).read_bytes())==r["sha256"] for r in rows)),None)
    if prior is None:
        raise ValueError("The recorded tagged artifacts could not be authenticated")
    tree=Path(tempfile.mkdtemp(prefix="label-oleans-",dir=work))
    scratch=tree/"setup"
    scratch.mkdir()
    tagged=dict(env,LEAN_PATH=str(tree)+os.pathsep+env["LEAN_PATH"])
    changes=[]
    final={}
    for r in rows:
        obj=tree/rel(r)
        obj.parent.mkdir(parents=True,exist_ok=True)
        reference=published[rel(r).as_posix()]
        if r["sha256"]==reference:
            obj.write_bytes((prior/rel(r)).read_bytes())
        else:
            source=rel(r).with_suffix(".lean").as_posix()
            label="/home/ubuntu/grh/src/lean/src/"+source
            relative=package_build(tc,tagged,work,scratch,r["module"],obj,"tree",source_label=source)
            labelled=package_build(tc,tagged,work,scratch,r["module"],obj,"tree",source_label=label)
            changes.append(dict(module=r["module"],relative_stdin_sha256=relative,
                relative_reproduces_tagged=relative==r["sha256"],published_label_sha256=labelled,
                published_label_matches=labelled==reference))
            print("source label: "+r["module"],flush=True)
        final[r["module"]]=sha(obj.read_bytes())==reference
    endpoint=record["tagged_endpoint_replay"]["module"]
    proc=subprocess.run([str(tc/"bin"/"leanchecker"),"-v",endpoint],env=tagged,cwd=work/"src",
                        capture_output=True,text=True)
    log=(proc.stdout+proc.stderr).strip()
    record["source_label_comparison"]=dict(input="identical pinned bytes via Lean --stdin for both labels",
        controls=changes,final_object_matches=final,endpoint_replay=dict(exit=proc.returncode,output=log))
    dump(path,record)
    if proc.returncode or log!="replaying "+endpoint:
        raise ValueError(log)


def replay_matched(tc,env,work,out,published):
    path=out/"external_objects.json"
    record=json.loads(path.read_text())
    final=record["source_label_comparison"]
    names=final["final_object_matches"]
    expected={r["module"] for r in json.loads((work/"prepared.json").read_text())["modules"]}
    if (record["pin"]!=PIN or record["manifest_sha256"]!=MANIFEST_SHA or not names
            or set(names)!=expected or not all(names.values())):
        raise ValueError("Complete the external object comparison before checking the matching set")
    def authenticated(tree):
        for mod in names:
            rel=Path(*mod.split(".")).with_suffix(".olean")
            obj=tree/rel
            if not obj.is_file() or sha(obj.read_bytes())!=published[rel.as_posix()]:
                return False
        return True
    tree=next((t for t in sorted(work.glob("label-oleans-*")) if authenticated(t)),None)
    if tree is None:
        raise ValueError("No complete scratch tree matches the published hashes")
    checked=dict(env,LEAN_PATH=str(tree)+os.pathsep+env["LEAN_PATH"])
    record["matched_kernel_replays"]=[]
    for mod in sorted(names):
        proc=subprocess.run([str(tc/"bin"/"leanchecker"),"-v",mod],env=checked,cwd=work/"src",
                            capture_output=True,text=True)
        log=(proc.stdout+proc.stderr).strip()
        record["matched_kernel_replays"].append(dict(module=mod,exit=proc.returncode,output=log))
        dump(path,record)
        if proc.returncode or log!="replaying "+mod:
            raise ValueError(log)
        print("replayed matching object: "+mod,flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for f in ("manifest","work","out","toolchain","mathlib"):
        ap.add_argument("--"+f,type=Path,required=True)
    mode=ap.add_mutually_exclusive_group()
    mode.add_argument("--all-packaged",action="store_true",help="Also rebuild the full analytic closure with its Lake package name")
    mode.add_argument("--source-label-controls",action="store_true",help="Use the completed tagged build to isolate source filename metadata")
    mode.add_argument("--replay-matched",action="store_true",help="Authenticate each final object against the external manifest and replay it")
    args = ap.parse_args()
    work,out,tc,mathlib = (getattr(args,k).resolve() for k in ("work","out","toolchain","mathlib"))
    external = args.manifest.read_bytes()
    if sha(external)!=MANIFEST_SHA:
        raise ValueError("Reference manifest digest mismatch")
    published = dict((path.removeprefix("./"),h) for h,path in
                     (line.split(maxsplit=1) for line in external.decode().splitlines()))
    build = json.loads((out/"lean_build.json").read_text())
    env,version = environment(tc,mathlib)
    if args.source_label_controls:
        return source_label_controls(tc,env,work,out,published)
    if args.replay_matched:
        return replay_matched(tc,env,work,out,published)
    warnings = {r["name"] for r in build["operations"] if r["stage"]=="module_compile" and "warning:" in r.get("output","")}
    rows = []
    for row in build["modules"]:
        n = row["module"]
        rel = n.replace(".","/")+".olean"
        local = sha((work/"oleans"/rel).read_bytes())
        rows.append(dict(module=n,local_sha256=local,published_sha256=published[rel],
                         identical=local==published[rel],compile_warning=n in warnings))
    # CharFamily imports Mathlib alone. Reuse identical source, options, directory and output name.
    # Vary only the package field between the two explicit setup files.
    name="Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily"
    scratch=work/"package-comparison"
    scratch.mkdir(exist_ok=True)
    output=scratch/"CharFamily.olean"
    rep=[]
    for package in (None,"tree"):
        h=package_build(tc,env,work,scratch,name,output,package)
        first=next(r for r in rows if r["module"]==name)
        rep.append(dict(package=package,sha256=h,matches_main_run=h==first["local_sha256"],
                        matches_published=h==first["published_sha256"]))
    record=dict(pin=PIN,published_manifest=URL,manifest_sha256=MANIFEST_SHA,
         published_rows=len(published),toolchain=version["version"],modules=rows,
         package_control_module=name,package_controls=rep)
    dest=out/"external_objects.json"
    dump(dest,record)
    if args.all_packaged:
        # Fresh dependency directory ensures every project import resolves to the tagged rebuild.
        tree=Path(tempfile.mkdtemp(prefix="tagged-oleans-",dir=work))
        tagged=dict(env,LEAN_PATH=str(tree)+os.pathsep+env["LEAN_PATH"])
        record["tagged_build"]=[]
        for r in rows:
            mod=r["module"]
            obj=(tree/Path(*mod.split("."))).with_suffix(".olean")
            if mod==name:
                obj.parent.mkdir(parents=True,exist_ok=True)
                obj.write_bytes(output.read_bytes())
                h=sha(obj.read_bytes())
            else:
                h=package_build(tc,tagged,work,scratch,mod,obj,"tree")
            record["tagged_build"].append(dict(module=mod,sha256=h,identical=h==r["published_sha256"]))
            dump(dest,record)
            print(f"package tree: {mod}",flush=True)
        endpoint=build["modules"][-1]["module"]
        proc=subprocess.run([str(tc/"bin"/"leanchecker"),"-v",endpoint],env=tagged,cwd=work/"src",
                            capture_output=True,text=True)
        record["tagged_endpoint_replay"]=dict(exit=proc.returncode,output=(proc.stdout+proc.stderr).strip(),module=endpoint)
        dump(dest,record)
        if proc.returncode or record["tagged_endpoint_replay"]["output"]!="replaying "+endpoint:
            raise ValueError(record["tagged_endpoint_replay"])


if __name__=="__main__":
    main()
