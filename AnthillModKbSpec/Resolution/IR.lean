-- The decision IR (S27): the programs decisions run on — predicates with modes
-- and kinds, rules, derived rules, denials, literals, queries — their checker,
-- the evidence classes P0 ⊂ P1 ⊂ P2 read per call pattern, the key semantics
-- with the Herbrand reduction, the relevant program of a query, finite under
-- P1 and computed, and S07's ground programs, where the IR expresses them, as
-- the P0 case.
import AnthillModKbSpec.Resolution.IR.Syntax
import AnthillModKbSpec.Resolution.IR.Check
import AnthillModKbSpec.Resolution.IR.Evidence
import AnthillModKbSpec.Resolution.IR.Semantics
import AnthillModKbSpec.Resolution.IR.Herbrand
import AnthillModKbSpec.Resolution.IR.Relevance
import AnthillModKbSpec.Resolution.IR.Parameters
import AnthillModKbSpec.Resolution.IR.Enumerate
import AnthillModKbSpec.Resolution.IR.Finite
import AnthillModKbSpec.Resolution.IR.RelevantProgram
import AnthillModKbSpec.Resolution.IR.Ground
