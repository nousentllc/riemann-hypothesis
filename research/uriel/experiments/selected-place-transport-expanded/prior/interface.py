"""Reproduce the literal old frame and host declarations in the joint Lean module."""

OLD_HOST_DIR = 'src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/'
ORBIT_SOURCE = 'src/Formalism/FrobeniusOrbits/Statement.lean'
FRAME_SOURCE = OLD_HOST_DIR + 'ZsmulGeneratorEqZeroOfProjection.lean'
HOST_SOURCE = OLD_HOST_DIR + 'ConjEMemHostFIff.lean'


def between(text, start, stop):
    begin = text.index(start)
    return text[begin:text.index(stop, begin)]


def source_excerpt(original):
    orbit = (original / ORBIT_SOURCE).read_text()
    frame = (original / FRAME_SOURCE).read_text()
    host = (original / HOST_SOURCE).read_text()
    return ''.join([
        'import Mathlib\nnoncomputable section\nnamespace Formalism.FrobeniusOrbits\n',
        between(orbit, 'def HostHyp (', 'theorem HostHyp.toHypQD'),
        between(orbit, 'abbrev HGrp', 'def cc (e'),
        'end Formalism.FrobeniusOrbits\nend\n',
        frame[frame.index('noncomputable section'):],
        '\n',
        between(host, 'open NumberField', 'namespace HostAx\n'),
        '\nend Formalism.HC\nend\n',
    ])
