-- Abstract machine states, continuations, proof evidence, and branch isolation (S04);
-- reading through answers, freshening, and scope-safe matching (S05); declared free
-- names as a machine invariant (S19); delayed goals, wakeups, and deferred proofs (S18);
-- reconstruction along a run, ordinary clause selection, and positive execution (S06).
import AnthillModKbSpec.Resolution.Machine.Store
import AnthillModKbSpec.Resolution.Machine.Instantiation
import AnthillModKbSpec.Resolution.Machine.Unification
import AnthillModKbSpec.Resolution.Machine.Evidence
import AnthillModKbSpec.Resolution.Machine.State
import AnthillModKbSpec.Resolution.Machine.Commands
import AnthillModKbSpec.Resolution.Machine.Reconstruction
import AnthillModKbSpec.Resolution.Machine.Program
import AnthillModKbSpec.Resolution.Machine.Positive
