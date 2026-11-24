"""Pinned Ollama adapter and durable, at-most-once session receipts."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import urllib.error
import urllib.request

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODEL = {"tag":"gpt-oss:20b", "digest":"17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7", "max_tokens":2048, "think":"low"}
SERVER = "0.40.18"
TIMEOUT_SECONDS = 900


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temp.replace(path)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hash_request(payload):
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


class BlockRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        raise RuntimeError("Local service redirect refused")


def local(path, payload=None):
    client = urllib.request.build_opener(urllib.request.ProxyHandler({}), BlockRedirect())
    body = json.dumps(payload).encode() if payload is not None else None
    request = urllib.request.Request("http://127.0.0.1:11434" + path, data=body,
                                     headers={"Content-Type":"application/json"})
    with client.open(request, timeout=TIMEOUT_SECONDS if body is not None else 15) as response:
        return json.load(response)


def verify_model():
    if local("/api/version")["version"] != SERVER:
        raise ValueError("Registered server version unavailable")
    available = local("/api/tags")["models"]
    if not any(m["name"] == MODEL["tag"] and m["digest"] == MODEL["digest"] for m in available):
        raise ValueError("Registered model digest unavailable")


def request_payload(messages, row, seed, stage_name):
    fields = {"verdict":{"type":"string","enum":["Y","N","U"]},
              "certificate":{"type":"array","items":{"type":"string","enum":list(row["states"])},
                             "minItems":1,"maxItems":8}}
    if stage_name == 'labels':
        fields = {sid: {'type': 'string', 'enum': ['Y','N']} for sid in row['survivors']}
    grammar = dict(type="object",properties=fields,required=list(fields),additionalProperties=False)
    return dict(model=MODEL["tag"], messages=messages, format=grammar, stream=False,
                keep_alive="9m", think=MODEL["think"],
                options=dict(seed=seed,temperature=0,num_ctx=8192,num_predict=MODEL["max_tokens"]))


def parse_answer(content, row, stage_name):
    try:
        answer = json.loads(content)
    except (ValueError,TypeError):
        return None
    if stage_name == 'labels':
        if (isinstance(answer,dict) and set(answer)==set(row['survivors'])
                and all(v in ('Y','N') for v in answer.values())):
            return answer
        return None
    if not isinstance(answer,dict) or set(answer) != {"certificate","verdict"}:
        return None
    cert = answer["certificate"]
    if (answer["verdict"] not in ("Y","N","U") or not isinstance(cert,list) or not 1 <= len(cert) <= 8
            or not all(isinstance(s,str) and s in row["states"] for s in cert)):
        return None
    return answer


def stage(path, payload, row, expected_hash, stage_name):
    request_hash = hash_request(payload)
    if request_hash != expected_hash:
        raise ValueError("Prepared payload does not match its preregistered hash")
    if path.exists():
        receipt = json.loads(path.read_bytes())
        if receipt["request_sha256"] != request_hash:
            raise ValueError("Saved receipt does not match")
        return receipt
    journal = path.with_suffix(".started")
    if journal.exists():
        started = json.loads(journal.read_bytes())
        if started["request_sha256"] != request_hash:
            raise ValueError("Interrupted job has different payload")
        receipt = dict(**started,status="interrupted",answer=None,ended=now())
        save(path,receipt)
        return receipt
    path.parent.mkdir(exist_ok=True,parents=True)
    save(path.parent/"request.json",payload)
    started = dict(request_sha256=request_hash, started=now())
    with journal.open("x") as stream:
        json.dump(started,stream)
    receipt = dict(**started,answer=None)
    try:
        result = local("/api/chat",payload)
        if result.get("model") != MODEL["tag"]:
            raise ValueError("Service returned another model")
        content = result.get("message",{}).get("content","")
        receipt.update(status="invalid",content=content,usage={key:result.get(key) for key in
            ("prompt_eval_count","eval_count","total_duration","load_duration","eval_duration","done_reason")})
        if result.get("done") and result.get("done_reason") == "stop":
            answer = parse_answer(content,row,stage_name)
            if answer is not None:
                receipt.update(status="ok",answer=answer)
    except (OSError,ValueError,KeyError,RuntimeError) as exc:
        receipt.update(status="error",error=str(exc)[:250])
    receipt["ended"] = now()
    save(path,receipt)
    return receipt
