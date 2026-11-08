-- The fast fragment: admission (S23) — modes, safety, data terms and the complete
-- and budgeted cost classes, profiles P1 and P2 with blockers, and the call bound —
-- and tabled evaluation (S24) — the completion's models as fixpoints, the abstract
-- fixpoints deciding No and Unknown, SLG resolution on the shared machine, the
-- termination of bounded runs without fuel, and the module's answers.
import AnthillModKbSpec.Resolution.Tabled.Graph
import AnthillModKbSpec.Resolution.Tabled.Fragment
import AnthillModKbSpec.Resolution.Tabled.Admission
import AnthillModKbSpec.Resolution.Tabled.Calls
import AnthillModKbSpec.Resolution.Tabled.Classes
import AnthillModKbSpec.Resolution.Tabled.Fixpoint
import AnthillModKbSpec.Resolution.Tabled.Abstract
import AnthillModKbSpec.Resolution.Tabled.AbstractSound
import AnthillModKbSpec.Resolution.Tabled.Witness
import AnthillModKbSpec.Resolution.Tabled.Multiset
import AnthillModKbSpec.Resolution.Tabled.Weight
import AnthillModKbSpec.Resolution.Tabled.Engine
import AnthillModKbSpec.Resolution.Tabled.EngineSound
import AnthillModKbSpec.Resolution.Tabled.Termination
import AnthillModKbSpec.Resolution.Tabled.Answer
