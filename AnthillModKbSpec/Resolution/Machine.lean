-- Abstract machine states, continuations, proof evidence, and branch isolation (S04);
-- reading through answers, freshening, and scope-safe matching (S05); declared free
-- names as a machine invariant (S19); delayed goals, wakeups, and deferred proofs (S18);
-- reconstruction along a run, ordinary clause selection, and positive execution (S06);
-- ground negation as failure evaluated in the same run (S07); left rules on selected
-- assumptions and compound clause heads, and the left strategy (S09); refutation search in
-- the completed program (S10); `ho_apply` conversion and whole-formula head matching (S11).
import AnthillModKbSpec.Resolution.Machine.Store
import AnthillModKbSpec.Resolution.Machine.Instantiation
import AnthillModKbSpec.Resolution.Machine.Unification
import AnthillModKbSpec.Resolution.Machine.Evidence
import AnthillModKbSpec.Resolution.Machine.State
import AnthillModKbSpec.Resolution.Machine.Commands
import AnthillModKbSpec.Resolution.Machine.Reconstruction
import AnthillModKbSpec.Resolution.Machine.Program
import AnthillModKbSpec.Resolution.Machine.Conversion
import AnthillModKbSpec.Resolution.Machine.Positive
import AnthillModKbSpec.Resolution.Machine.Negation
import AnthillModKbSpec.Resolution.Machine.LeftRules
import AnthillModKbSpec.Resolution.Machine.LeftStrategy
import AnthillModKbSpec.Resolution.Machine.Refutation
-- Open atoms reached through an open predicate's marked case (S22).
import AnthillModKbSpec.Resolution.Machine.OpenAtoms
