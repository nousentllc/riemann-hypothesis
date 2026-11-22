"""Pinned source checks and a deliberately partial lexical dependency graph."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = '40e56bab026552e089d7afcfeff08d2defb9c005'
BASE = '08188ff0c6dd02dfec0bd65d30765862e9db56b7'
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def mask_comments(text):
    """Preserve positions while masking nested Lean comments and string literals.

    This is a small lexer, not a Lean parser; quoted identifiers/macros may need
    richer parsing. Namespace resolution and implicit references are not inferred.
    """
    out=list(text);i=0;depth=0;line=False;string=False
    while i<len(text):
        pair=text[i:i+2]
        if line:
            if text[i]=='\n':line=False
            else:out[i]=' '
            i+=1;continue
        if depth:
            if pair=='/-':out[i:i+2]='  ';depth+=1;i+=2;continue
            if pair=='-/':out[i:i+2]='  ';depth-=1;i+=2;continue
            if text[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if text[i]=='\\' and i+1<len(text):out[i:i+2]='  ';i+=2;continue
            if text[i]=='"':string=False
            if text[i]!='\n':out[i]=' '
            i+=1;continue
        if pair=='/-':out[i:i+2]='  ';depth=1;i+=2;continue
        if pair=='--':out[i:i+2]='  ';line=True;i+=2;continue
        if text[i]=='"':out[i]=' ';string=True
        i+=1
    return ''.join(out)


def declarations(text):
    masked=mask_comments(text)
    pattern=r'(?m)^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|structure|axiom)\s+([^\s(:]+)'
    matches=list(re.finditer(pattern,masked));result=[]
    for i,m in enumerate(matches):
        end=matches[i+1].start() if i+1<len(matches) else len(masked)
        segment=masked[m.start():end]
        result.append(dict(name=m.group(1),line=text[:m.start()].count('\n')+1,
                           end_line=text[:end].count('\n')+1,masked=segment,
                           statement=segment.split(':=',1)[0].strip(),
                           body=segment.split(':=',1)[1] if ':=' in segment else ''))
    return result


def contains_token(text,token):
    return re.search(r'(?<![\w.])'+re.escape(token)+r'(?![\w])',text) is not None


def get_decl(text,name):
    hits=[d for d in declarations(text) if d['name']==name or d['name'].endswith('.'+name)]
    if len(hits)!=1:raise ValueError(f'Expected unique declaration {name}, got {len(hits)}')
    return hits[0]


def git(*args):
    return subprocess.check_output(['git',*args],cwd=REPO)


def audit():
    trace=json.loads((HERE.parents[1]/'SOURCE_TRACE.json').read_text())
    paths={r['path']:r['sha256'] for r in trace['files']}
    extras=['src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean',
            'src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean',
            'src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean',
            'src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean',
            'src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean',
            'src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean',
            'src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean',
            'src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean',
            'src/Formalism/SizeWindowBrackets/SChain.lean','src/Supplements/Kernels/MainTheoremsAll.lean']
    paths.update({p:None for p in extras})
    contents={};records=[]
    for path,expected in paths.items():
        raw=git('show',PIN+':'+path);digest=hashlib.sha256(raw).hexdigest()
        if expected and digest!=expected:raise ValueError('Original pin hash mismatch: '+path)
        contents[path]=raw.decode()
        records.append(dict(path=path,sha256=digest,prior_trace_match=expected==digest if expected else None,
                            bytes=len(raw),lines=len(raw.splitlines()),
                            url=f'https://github.com/nousentllc/riemann-hypothesis/blob/{PIN}/{path}'))
    def pathof(stem):
        hits=[p for p in contents if Path(p).stem==stem]
        if len(hits)!=1:raise ValueError(stem)
        return hits[0]
    # Each item asserts only a visible body reference, not necessity or elaboration.
    specifications=[
      ('Main','riemannHypothesis',['rhOfAll']),
      ('Main','riemannZeta_eq_zero_re',['rhOfAll']),
      ('Main','LFunction_ne_zero_of_half_lt_re',['allChi']),
      ('Main','LFunction_eq_zero_re',['claimAll']),
      ('Main','LFunction_eq_zero_re_of_isPrimitive',['critAll']),
      ('MainTheorems','allChi',['UpperTheory.FinalTheorems.everyCharacter']),
      ('MainTheorems','rhOfAll',['Formalism.VW.rh_of_every','allChi']),
      ('MainConclusion','everyCharacter',['UpperTheory.FinalTheorems.everyCharacter_of_row','UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter']),
      ('MainConclusion','everyCharacter_of_row',['UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin','UpperTheory.Zero.LLC.recTExists','UpperTheory.One.vwin_of_row']),
      ('EveryCharacterOfLiteratureOfVWin','every_character_of_literature_of_vWin',['every_character_of_theta_integrals_local_matching']),
      ('SiegelEisensteinSecondTermHypotheses','every_character_of_theta_integrals_local_matching',['UpperTheory.Top.every_character_of_green_v_win']),
      ('TopPlug','every_character_of_green_v_win',['UpperTheory.Top.imprimitive','_root_.UpperTheory.Top.zero_free_all_of_green_v_win']),
      ('TopPlug','zero_free_all_of_green_v_win',['UpperTheory.Top.zeroFreeAll_of_topG','_root_.UpperTheory.Top.shape_closed_link_n_of_green']),
      ('ZeroFreeAllOfTopG','zeroFreeAll_of_topG',['zeroFreeOn_of_tiedWin_cyc','UpperTheory.Comparison₂.level_gm_le_on_family_scales','UpperTheory.Comparison₂.formB']),
      ('LevelGmLeOnFamilyScales','level_gm_le_on_family_scales',['windowInequality_of_artinInputs']),
      ('WindowInequalityOfArtinInputs','windowInequality_of_artinInputs',['core_gm']),
      ('CoreGm','core_gm',['Deduction.ch_core','Deduction.ch_top','sigA_le']),
      ('Imports','formB',['Deduction.zeroFree_of_rpow_window']),
      ('ZeroFreeOfRpowWindow','zeroFree_of_rpow_window',['lemmaL','windowHyp_of_rpow']),
      ('lemmaL','lemmaL',['poleData','landau_window','windowHypU_of_windowHyp']),
      ('landauWindow','landau_window',['landau_window_key','landau_window_contra']),
      ('landauWindow','landau_window_key',['landau_tails','landau_window_ineq']),
      ('Window','window',['UpperTheory.V.Win.window1']),
      ('Window1','window1',['ih']),
      ('MajAtAddRight','slope_good_ge',['Formalism.ExtensionFiltration.goodBadCut','numeric']),
      ('CovolumeFromGramAndBounds','lcv_le',['GlobalTheory.CutNum.slope_good_ge']),
    ]
    nodes=[];edges=[];failures=[]
    for stem,name,refs in specifications:
        path=pathof(stem);decl=get_decl(contents[path],name)
        node=f'{path}::{decl["name"]}'
        nodes.append(dict(id=node,path=path,name=decl['name'],line=decl['line'],statement=decl['statement'],
                          url=f'https://github.com/nousentllc/riemann-hypothesis/blob/{PIN}/{path}#L{decl["line"]}'))
        for ref in refs:
            found=contains_token(decl['body'],ref)
            edges.append(dict(source=node,reference=ref,witnessed_in_body=found,
                              kind='source_body_reference',elaborated_dependency=False))
            if not found:failures.append(f'{name} -> {ref}')
    guards=[('LandauZeroFreeCriterion','PoleData','0 < c.re ∧ c.im = 0'),
            ('LandauZeroFreeCriterion','WindowHypU','∀ η : ℝ, 0 < η → ∀ U₀ : ℝ'),
            ('MajAtAddRight','numeric','δ ≤ 1 / 12'),
            ('GrowthBoundGivesRiemannHypothesis','SizeWindows','26 ≤ x ^ (3 * ε / 8)'),
            ('SecondBound','Good','(e : ℝ) ≤ x ^ Ct → (e : ℝ) ≤ x ^ eta'),
            ('PairRowIffQdRows','RankVal','9 / 2 + 10 * s.eps')]
    guarded=[]
    for stem,name,token in guards:
        p=pathof(stem);d=get_decl(contents[p],name);present=token in d['masked']
        guarded.append(dict(path=p,declaration=name,line=d['line'],token=token,present=present,
                            mutation_detected=token not in d['masked'].replace(token,'MUTATED',1)))
        if not present:failures.append('guard '+name)
    modules={p[4:-5].replace('/','.'):p for p in contents}
    imports=[]
    for p,txt in contents.items():
        for m in re.findall(r'(?m)^import\s+(\S+)',mask_comments(txt)):
            imports.append(dict(source=p,module=m,resolved_in_selected_corpus=m in modules,
                                kind='module_import',theorem_dependency=False))
    bait='theorem foo : True := by\n  /- nested /- fake -/ fake -/\n  -- fake\n  trivial\n'
    ignored=not contains_token(get_decl(bait,'foo')['body'],'fake')
    try:toolchains=subprocess.check_output(['elan','toolchain','list'],text=True).strip()
    except (OSError,subprocess.CalledProcessError):toolchains='unavailable'
    return dict(source_pin=PIN,research_parent=BASE,prior_trace_files=len(trace['files']),
                files=records,nodes=nodes,edges=edges,imports=imports,guards=guarded,failures=failures,
                comment_bait_ignored=ignored,full_dependency_closure=False,axiom_inventory_checked=False,
                verification=dict(original_toolchain=git('show',PIN+':lean-toolchain').decode().strip(),
                    research_toolchain=git('show',BASE+':lean-toolchain').decode().strip(),
                    installed_toolchains=toolchains,lake_directory_present=(REPO/'.lake').exists(),
                    full_build_attempted=False,kernel_replay_attempted=False,
                    reason='Pinned v4.33.1 toolchain and dependencies are absent; selected sparse source only. Full 175187-module build is outside this lightweight CPU run. No build failure is claimed.',
                    external_record='https://math.mit.edu/~drew/grh/',external_record_date='2026-11-22 16:20 UTC'))
