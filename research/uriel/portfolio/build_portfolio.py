"""Build the Riemann study index, a static search page, and a GitHub preview."""

import argparse
import html
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


HERE = Path(__file__).resolve().parent
INDEX = json.loads((HERE / "study-index.json").read_text(encoding="utf-8"))
TRACKS = INDEX["tracks"]
REPO = INDEX["repository"]
DATE = INDEX["date"]
STUDIES = sum(len(track["studies"]) for track in TRACKS)
RELATED = sum(len(track["related"]) for track in TRACKS)

LATEST = next(
    study
    for track in TRACKS
    for study in track["studies"]
    if study["id"] == "global-frobenius"
)
WRITTEN_SELECTION = (
    "The written theorem jointly chooses a prime and good orbit on the original "
    "weighted host while keeping the retained set fixed. The lift-summed "
    "premium pays the original tau and any fixed nonnegative multiple of io "
    "with at least mb′/4 left. Six Lean modules check source accounting, "
    "predecessors, finite budgets, ramps and transport. The late asymptotic "
    "choice and Fourier strip estimate are written arguments."
)


def study_url(study):
    return f"{REPO}/tree/{study['commit']}/{study['path']}"


def write_markdown():
    lines = [
        "# Riemann proof studies",
        "",
        f"{STUDIES} experiment branches and {RELATED} additional editions or substudies. "
        f"Links are pinned to the Git state audited on {DATE}.",
        "",
        "![Six research tracks from the original arithmetic-window formalization to "
        "same-set gain, local densities and model reading tests](research-map.png)",
        "",
        "[Open the branch index below](#studies-by-research-question) · "
        "[Download the searchable HTML map](research-map.html) · "
        "[Machine-readable index](study-index.json) · "
        "[Older research ZIPs](legacy-packages/README.md) · "
        "[Publication archive](publication-archive/README.md)",
        "",
        "## Where to start",
        "",
        "- To understand the common analytic observable, read the "
        f"[windows and remainder study]({study_url(TRACKS[0]['studies'][-1])}) and the "
        f"[joint critical edition]({study_url(TRACKS[0]['related'][-1])}).",
        "- For the third source edition, see the [compact proof audit](compact-proof-audit/README.md). "
        "It follows the signed auxiliary cutoff and the cost of the missing independent forms.",
        "- To follow one arithmetic choice, start at "
        f"[PairRow and the core]({study_url(TRACKS[1]['studies'][0])}), then read the "
        f"[fixed-datum study]({study_url(TRACKS[1]['related'][0])}) and "
        f"[selected-place transport]({study_url(TRACKS[1]['related'][1])}).",
        "- To reproduce a standalone local theorem, read "
        f"[the ramified Gram-fiber bridge]({study_url(TRACKS[4]['studies'][7])}) and "
        f"[the square-dilate extension]({study_url(TRACKS[4]['studies'][8])}).",
        "- To see how those local questions reach the original proof, follow the "
        "[declaration route to the rank-one normalization](declaration-graph/README.md).",
        "",
        "## Latest result",
        "",
        WRITTEN_SELECTION,
        "",
        f"[Paper, replay and controls]({study_url(LATEST)}) · "
        f"[Commit {LATEST['commit'][:7]}]({REPO}/commit/{LATEST['commit']})",
        "",
        "## Local-density checkpoint",
        "",
        "The [ramified companion fiber](ramified-companion/README.md) has written mass "
        "$2-2/256^k$ at $4^k(1+\\sqrt{2})u^2$. The normalized counts stabilize at depth $4k+2$. "
        "The checkpoint includes exact finite controls and a kernel replay of the modulo-two obstruction. "
        "The full Lean proof of stabilization and transport remains open.",
        "",
        "## How the tracks connect",
        "",
        "The cohomology and host studies identify which data the original "
        "arithmetic estimates share. The orbit studies quantify one cost of that "
        "selection. The Frobenius studies carry a different gain comparison "
        "through later arithmetic terms on one host. The local-density studies "
        "follow automorphic normalization inputs at a finite place. The model "
        "studies test how readers handle incomplete records.",
        "",
        "These links describe reading order and mathematical context. Each release "
        "states its own import dependencies and the scope of its formal replay.",
        "",
        "## Studies by research question",
    ]
    for track in TRACKS:
        lines += [
            "", f"### {track['title']}", "", track["question"], "", track["finding"], "",
            "| Study | Question or result | Commit |",
            "| --- | --- | --- |",
        ]
        for study in track["studies"] + track["related"]:
            sha = study["commit"]
            lines.append(
                f"| [{study['title']}]({study_url(study)}) | {study['detail']} | "
                f"[`{sha[:7]}`]({REPO}/commit/{sha}) |"
            )
    lines += [
        "", "## Evidence and provenance", "",
        "- The studies distinguish exact finite controls, written deductions from "
        "the archived source, and local Lean kernel replays. Read the evidence "
        "and verification sections at each release for its hypotheses, pins, and limits.",
        "- The initial source reading is in [PROOF_CONTEXT.md](../PROOF_CONTEXT.md) "
        "with declaration anchors in [SOURCE_TRACE.json](../SOURCE_TRACE.json).",
        "- The branch list verifies where the studies were published. Ten GitHub ZIPs "
        "matched the local release copies byte for byte. Each archive contained one "
        "TeX source and its PDF. Their Git blob hashes are in the "
        "[machine-readable index](study-index.json).",
        "- The study replays are documented in the linked releases. This portfolio "
        "audit verified publication and package identity.",
    ]
    for base in INDEX["baseline"]:
        lines.append(
            f"- Baseline `{base['branch']}` · "
            f"[`{base['sha'][:7]}`]({REPO}/tree/{base['sha']})."
        )
    lines += [
        "", "## Rebuild the index", "",
        "Run `python3 build_portfolio.py` from this folder with Pillow installed. "
        "The [generator](build_portfolio.py) reads `study-index.json` and writes this "
        "README, the HTML, and the PNG. An optional `--font-dir` points to the "
        "Georgia and Arial fonts or to DejaVu Serif and Sans.",
    ]
    (HERE / "README.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_html():
    esc = html.escape
    buttons = ['<button type="button" data-track="" aria-pressed="true">All studies</button>']
    cards = []
    for track in TRACKS:
        name = esc(track["title"])
        tid = esc(track["id"])
        color = track["color"]
        buttons.append(
            f'<button type="button" data-track="{tid}" aria-pressed="false" '
            f'style="--track:{color}">{name}</button>'
        )
        rows = []
        related_ids = {study["id"] for study in track["related"]}
        for study in track["studies"] + track["related"]:
            caption = "Related edition" if study["id"] in related_ids else study["commit"][:7]
            rows.append(
                f'<li><a href="{esc(study_url(study))}">{esc(study["title"])}</a>'
                f'<span class="stamp">{caption}</span><p>{esc(study["detail"])}</p></li>'
            )
        cards.append(
            f'<section aria-labelledby="h-{tid}" class="track" data-section="{tid}" style="--track:{color}">'
            f'<h2 id="h-{tid}">{name}</h2><p class="question">{esc(track["question"])}</p>'
            f'<p class="route">{esc(track["route"])}</p><p>{esc(track["finding"])}</p>'
            f'<ul class="studies">{"".join(rows)}</ul></section>'
        )
    page = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Riemann proof studies · Nous</title>
<style>
:root { --ink:#202c32; --dim:#52616b; --line:#ccd3d4; --paper:#f5f3ec; --white:#fffefa; }
* { box-sizing:border-box; }
body { margin:0; color:var(--ink); background:var(--paper); font:16px/1.55 system-ui,sans-serif; }
main { width:min(1100px, 100% - 44px); margin:0 auto; padding:3.4rem 0; }
h1, h2 { font-family:Georgia,serif; line-height:1.05; font-weight:normal; }
h1 { font-size:clamp(2.55rem,8vw,5.9rem); margin:.35rem 0 1rem; letter-spacing:-.04em; }
h2 { font-size:2rem; margin:0 0 .6rem; }
p { margin:.6rem 0; }
a { color:#145279; text-underline-offset:.16em; }
a:hover { color:#853e25; }
:focus-visible { outline:3px solid #30678b; outline-offset:4px; }
.small { color:var(--dim); font-size:.9rem; }
.lead { font-size:1.15rem; max-width:48rem; }
.latest { background:#24343b; color:#fffefa; padding:1.25rem 1.5rem; margin:1.8rem 0; }
.latest h2 { font-size:1.65rem; }
.latest p { max-width:54rem; }
.latest a { color:#b0ebdf; }
.controls { border-block:1px solid var(--line); padding:1rem 0 .85rem; }
label { font-weight:650; display:block; margin-bottom:.25rem; }
input { font:inherit; color:inherit; border:1px solid #74858d; background:var(--white);
        border-radius:4px; padding:.6rem .75rem; width:min(100%,36rem); }
.buttons { display:flex; flex-wrap:wrap; gap:.4rem; margin-top:.7rem; }
button { font:inherit; font-size:.86rem; border:1px solid #87969a; border-radius:4px;
         padding:.37rem .62rem; background:var(--white); color:var(--ink); cursor:pointer; }
button[aria-pressed="true"] { background:var(--track,#24343b); color:white; border-color:transparent; }
.track { border-top:4px solid var(--track); background:var(--white);
         padding:1.15rem 1.4rem 1.3rem; margin:1.4rem 0; }
.question { font-weight:650; }
.route { color:var(--track); font-weight:660; }
.studies { padding:0; list-style:none; display:grid; grid-template-columns:repeat(2,1fr);
           column-gap:1.4rem; margin:1rem 0 0; }
.studies li { border-top:1px solid var(--line); padding:.7rem 0 .5rem; }
.studies a { font-weight:650; }
.studies p { color:var(--dim); margin:.28rem 0; }
.stamp { padding-left:.45rem; color:var(--dim); font-size:.74rem; }
footer { border-top:1px solid var(--line); padding-top:1rem; }
[hidden] { display:none !important; }
@media(max-width:620px) {
  main { width:calc(100% - 28px); padding:1.8rem 0; }
  .studies { grid-template-columns:1fr; }
  .track { padding:.95rem; }
}
</style>
</head>
<body>
<main>
<header>
<p class="small">Nous Research · @DATE@</p>
<h1>Riemann proof studies</h1>
<p class="lead">Six ways into the arithmetic windows, the same-set gain, the local measure calculations, and the experiments on how agents read evidence.</p>
<p><a href="@GITINDEX@">GitHub study index</a> · <a href="@SOURCE@">Original proof source</a></p>
<p><a href="@GITINDEX@/compact-proof-audit">Compact proof audit</a> ·
<a href="@GITINDEX@/declaration-graph">Declaration route to rank-one normalization</a> ·
<a href="@GITINDEX@/ramified-companion">Ramified companion checkpoint</a></p>
</header>
<aside class="latest">
<h2>Latest study · Frobenius premium in the arithmetic window</h2>
<p>@LATESTSUMMARY@</p>
<a href="@LATESTURL@">Read the paper and replay</a>
</aside>
<div class="controls" hidden>
<label for="study-search">Find a study</label>
<input id="study-search" type="search" placeholder="Search titles and results">
<div class="buttons">@BUTTONS@</div>
<p id="result-count" class="small" aria-live="polite"></p>
</div>
@CARDS@
<footer class="small">
<p>Links pin @STUDIES@ experiment branches and @RELATED@ additional editions or substudies.
Evidence ranges from finite controls and model runs to written mathematics and local kernel replay.</p>
</footer>
</main>
<script>
const controls = document.querySelector('.controls');
const input = document.getElementById('study-search');
const buttons = [...document.querySelectorAll('[data-track]')];
const tracks = [...document.querySelectorAll('[data-section]')];
const count = document.getElementById('result-count');
let selected = '';
function filter() {
  const terms = input.value.toLocaleLowerCase().trim().split(/\s+/).filter(Boolean);
  let visible = 0;
  for (const track of tracks) {
    const inTrack = selected === '' || track.dataset.section === selected;
    const title = track.querySelector('h2').textContent.toLocaleLowerCase();
    const items = [...track.querySelectorAll('li')];
    let shown = 0;
    for (const item of items) {
      const text = title + ' ' + item.textContent.toLocaleLowerCase();
      item.hidden = !inTrack || !terms.every(term => text.includes(term));
      if (!item.hidden) shown++;
    }
    track.hidden = shown === 0;
    visible += shown;
  }
  count.textContent = visible === 0 ? 'No studies match your search.' :
    visible + (visible === 1 ? ' entry shown' : ' entries shown');
}
for (const button of buttons) {
  button.addEventListener('click', () => {
    selected = button.dataset.track;
    for (const peer of buttons) peer.setAttribute('aria-pressed', String(peer === button));
    filter();
  });
}
input.addEventListener('input', filter);
controls.hidden = false;
filter();
</script>
</body>
</html>
"""
    for key, value in {
        "DATE": DATE, "LATESTSUMMARY": esc(WRITTEN_SELECTION), "LATESTURL": study_url(LATEST),
        "BUTTONS": "".join(buttons), "CARDS": "".join(cards),
        "GITINDEX": f"{REPO}/tree/research/uriel/research/uriel/portfolio",
        "SOURCE": f"{REPO}/tree/40e56bab026552e089d7afcfeff08d2defb9c005",
        "STUDIES": STUDIES, "RELATED": RELATED,
    }.items():
        page = page.replace(f"@{key}@", str(value))
    (HERE / "research-map.html").write_text(page, encoding="utf-8")


def system_fonts(font_dir):
    families = (
        ("Georgia.ttf", "Arial.ttf", "Arial Bold.ttf"),
        ("DejaVuSerif.ttf", "DejaVuSans.ttf", "DejaVuSans-Bold.ttf"),
    )
    locations = [font_dir] if font_dir else [
        Path("/System/Library/Fonts/Supplemental"),
        Path("/usr/share/fonts/truetype/dejavu"),
    ]
    for root in locations:
        for family in families:
            paths = [root / font for font in family]
            if all(path.is_file() for path in paths):
                return paths
    raise SystemExit("Use --font-dir with Georgia/Arial or DejaVu font files.")


def write_image(font_dir):
    serif, sans, bold = system_fonts(font_dir)
    image = Image.new("RGB", (1360, 1000), "#f5f3ec")
    draw = ImageDraw.Draw(image)
    font = ImageFont.truetype
    ink, quiet = "#202c32", "#4b5b60"
    x = 46
    draw.text((x, 35), "Nous Research  /  26 November 2026", font=font(bold, 23), fill=quiet)
    draw.text((x, 73), INDEX["title"], font=font(serif, 74), fill=ink)
    draw.text((x, 163), "How the studies fit together", font=font(sans, 29), fill=quiet)
    draw.text((1314, 164), f"{STUDIES} study branches", font=font(bold, 24), fill=quiet, anchor="ra")
    lane_titles = [
        "Architecture & prime windows",
        "Witnesses & exceptional sets",
        "Orbit losses & recovery",
        "Same-set Frobenius & gain",
        "Local density & normalization",
        "Proof-reading experiments",
    ]
    lanes = [
        ("Original localized Landau → prime ramps → readable remainder",
         "The same smoothed observable supports two different analytic hypotheses."),
        ("PairRow and core → fixed slots → two selections across a gap",
         "The chosen field and set govern which conclusions carry across selections."),
        ("Weighted orbit test → actual fallback → stationary 64-cycle",
         "The uniform stationary guarantee reaches 10.1190% in its specified construction."),
        ("Spacing → two odd partners → b′/4 premium → τ and io",
         "The newest result keeps the set fixed through the window’s arithmetic costs."),
        ("Gaussian 3/4 and 63/64 → ramified 257/128 → growth and charts",
         "Counts become measures through lifting, Haar normalization and transport."),
        ("One lookup → marking and filtering → row labels → quantifiers",
         "Controlled model runs test the evidence a reader uses to reach a verdict."),
    ]
    for index, (track, title, (route, explanation)) in enumerate(
        zip(TRACKS, lane_titles, lanes, strict=True)
    ):
        y = 215 + 111 * index
        color = track["color"]
        title_font = font(bold, 23)
        route_font = font(bold, 25)
        explanation_font = font(sans, 22)
        if (
            draw.textlength(title, font=title_font) > 350
            or draw.textlength(route, font=route_font) > 842
            or draw.textlength(explanation, font=explanation_font) > 842
        ):
            raise ValueError(f"Research map label exceeds its column: {title}")
        draw.rectangle((x, y, 1314, y + 99), fill="#fffefa", outline="#d9ddd8")
        draw.rectangle((x, y, x + 7, y + 99), fill=color)
        draw.text((x + 25, y + 16), title, font=title_font, fill=ink)
        draw.text((x + 25, y + 53), f"{len(track['studies'])} branches", font=font(sans, 20), fill=quiet)
        draw.text((440, y + 14), route, font=route_font, fill=color)
        draw.text((440, y + 54), explanation, font=explanation_font, fill=ink)
    draw.line((x, 901, 1314, 901), fill="#aab9b7", width=1)
    draw.text((x, 921), "Read the arrows as a study sequence. Each release identifies its Lean imports and checks.",
              font=font(sans, 22), fill=quiet)
    draw.text((x, 951), "Evidence includes source traces, written proofs, exact controls, kernel replays and model runs.",
              font=font(sans, 22), fill=quiet)
    image.convert("P", palette=Image.Palette.ADAPTIVE, colors=96).save(
        HERE / "research-map.png", optimize=True
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--font-dir", type=Path)
    args = parser.parse_args()
    write_markdown()
    write_html()
    write_image(args.font_dir)
