"""Legacy CSTZ implementations — frozen, accessible via cstz.legacy.

The classical SPPF stack and the PFF parallel implementation live here.
Use `from cstz.legacy.core import SPPF` etc. for explicit access.
"""

from cstz.legacy.core import SPPF, UnionFind, Fiber, FiberClass
from cstz.legacy.python_classifier import factorize
from cstz.legacy.byte_classifier import factorize_bytes
