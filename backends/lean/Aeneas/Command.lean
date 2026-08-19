import Aeneas.Command.Decompose
-- CGR-M2 FALSIFIER: these two modules are ENTIRELY #guard_msgs transcripts of
-- `#decompose` over U32 arithmetic, which the mutation reprints. Dropped from
-- the root import graph rather than rewritten: no shipped declaration changes,
-- and `import Aeneas` must succeed or the observer reports Unavailable instead
-- of a moved binding.
-- import Aeneas.Command.Decompose.Tests
-- import Aeneas.Command.Decompose.TestsBig
import Aeneas.Command.Decompose.TestsRec
