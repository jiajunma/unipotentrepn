"""
combunipotent - Combinatorics of Unipotent Representations of Classical Groups

This package provides tools for computing unipotent representations attached to
nilpotent orbits of classical Lie groups (Sp, SO, Mp), using:

- Springer correspondence and Lusztig symbols (tool.py)
- DRC (dot-r-c) diagrams parametrizing representations (drc.py)
- Local systems on nilpotent orbits with theta lifting (LS.py)
- DRC-LS matching via theta lifting framework (drclift.py)
- Lifting graph visualization (lsdrcgraph.py)
- Recursive counting formulas with signature polynomials (recursive.py)

Root system types:
    C  : Sp(2n) - symplectic group
    D  : SO(2n) - even special orthogonal group
    B  : SO(2n+1) - odd special orthogonal group
    M  : Mp(2n) - metaplectic group (double cover of Sp)
    CS : compact/split symplectic variant
    DS : quaternionic orthogonal variant
"""
from .tool import *
from .combunip import *
from .drc import *
from .LS  import *
from .drclift import *
#from .liftgraph import *
from .lsdrcgraph import *
from .recursive import countunip, countB, countC, countD, countM, countCS, countDS
