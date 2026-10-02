"""Generate an independent, compact Challenge with genuine verbatim definitions.
Only selected theorem proofs are holes. Supporting proof implementations stay
in the reusable library. No candidate-local modules are imported by Challenge.
"""
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent

SOURCES = [
    ('JM/Defs.lean', 'JM'),
    ('JM/Quantitative.lean', 'JM.Quantitative'),
    ('JM/Sharp.lean', 'JM.Sharp'),
    ('JM/Frontier.lean', 'JM.Sharp'),
    ('JM/Corollaries.lean', 'JM'),
    ('JM/Binary.lean', 'JM.Binary'),
    ('JM/ContinuousAuction.lean', 'JM.ContinuousAuction'),
]
THEOREMS = [
    'JM.Quantitative.welfare_incentive_bound',
    'JM.Sharp.welfare_incentive_frontier',
    'JM.Sharp.frontier_attained',
    'JM.Sharp.feasible_iff',
    'JM.Sharp.exact_bic_loss',
    'JM.Sharp.exact_bic_attained',
    'JM.jehiel_moldovanu_impossibility',
    'JM.Binary.utility_integrable',
    'JM.Binary.congruence',
    'JM.Binary.aligned_ex_post',
    'JM.Binary.implementation_iff',
    'JM.Binary.efficient_bic_exists_iff',
    'JM.ContinuousAuction.uniform_probability',
    'JM.ContinuousAuction.prior_probability',
    'JM.ContinuousAuction.joint_probability',
    'JM.ContinuousAuction.welfare_difference',
    'JM.ContinuousAuction.utility_integrable',
    'JM.ContinuousAuction.impossibility',
]

def declarations(src):
    # These modules use ordinary top-level declarations and no mutual blocks.
    matches = list(re.finditer(r'(?m)^(abbrev|def|theorem|lemma) (\w+)\b', src))
    for ix,m in enumerate(matches):
        end = matches[ix+1].start() if ix+1<len(matches) else src.rindex('\nend\n')
        raw = src[m.start():end]
        # Strip the next declaration's documentation / local options.
        raw = re.split(r'\n/--|\nset_option |\nomit ',raw,maxsplit=1)[0].rstrip()
        yield m.group(1),m.group(2),raw

def render():
    out=['module', '', 'public import Mathlib.Algebra.BigOperators.Group.Finset.Basic',
         'public import Mathlib.Basic.ENNReal.BigOperators', 'public import Mathlib.Data.Finset.Max',
         'public import Mathlib.Data.Fintype.Pi', 'public import Mathlib.Data.Fintype.Prod',
         'public import Mathlib.Basic.Real.Basic', 'public import Mathlib.Logic.Function.Basic',
         'public import Mathlib.Probability.Distributions.Uniform',
         'public import Mathlib.MeasureTheory.Integral.Bochner.Basic',
         'public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic',
         'public import Mathlib.LinearAlgebra.Dual.Lemmas',
         'public import Mathlib.Analysis.Normed.Module.Basic', 'public import Mathlib.Tactic', '',
         '/-! Continuous binary coefficient congruence and explicit-transfer implementation,',
         'with an independent uniform-square auction impossibility for all a,b>0.',
         'The earlier sharp finite welfare/incentive frontier is separately retained.',
         'Genuine definitions are repeated verbatim; only selected theorem proofs are holes.',
         'No full arbitrary-alternative theorem, novelty or hosted verdict is claimed. -/', '',
         '@[expose] public section', '']
    defs=[];found=[]
    for file,ns in SOURCES:
        src=(ROOT/file).read_text()
        out += [f'namespace {ns}', 'open scoped BigOperators NNReal', 'noncomputable section', '']
        if ns=='JM.Quantitative':
            out += ['variable {T O K : Type*} [Fintype T] [Fintype O] [Fintype K]', '']
        if ns=='JM.Binary':
            out += ['open MeasureTheory', 'variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]', '  [MeasurableSpace Ω]', '']
        if ns=='JM.ContinuousAuction':
            out += ['open MeasureTheory Set', 'attribute [local instance] Measure.Subtype.measureSpace', '']
        for kind,name,raw in declarations(src):
            fullname=ns+'.'+name
            if kind in ('def','abbrev') or fullname=='JM.argmax_nonempty':
                if file=='JM/Defs.lean' and name=='weight':
                    out+=['variable (π : (i : Agent) → PMF (T i))', '']
                out += [raw,'']
                if kind=='def': defs.append(fullname)
            elif fullname in THEOREMS:
                statement=raw[:raw.index(':=')].rstrip()
                out += [statement+' := by\n  sorry','']
                found.append(fullname)
        out+=['end',f'end {ns}','']
    assert set(found)==set(THEOREMS),(found,THEOREMS)
    config={'challenge_module':'Challenge','solution_module':'Solution',
            'definition_names':defs,'theorem_names':THEOREMS,
            'permitted_axioms':['propext','Quot.sound','Classical.choice']}
    return '\n'.join(out),config

if __name__=='__main__':
    source,config=render()
    (ROOT/'Challenge.lean').write_text(source)
    (ROOT/'comparator.json').write_text(json.dumps(config,indent=2)+'\n')
    print('Challenge:',len(source.encode()),'bytes,',len(source.splitlines()),'lines; selected',len(config['definition_names']),'definitions and',len(THEOREMS),'theorems')
