import AnthillModKbSpec.Models.InductionModel
import AnthillModKbSpec.Resolution.CertifiedRefutation

namespace AnthillModKbSpec.InductionModel

open Semantics

def naf : NafFailure String Unit Symbol := CertifiedRefutation.failureEvidence model kb

theorem naf_adequate : model.FailureAdequate kb naf :=
  CertifiedRefutation.failureAdequate model complement kb

theorem sound {context : ProofContext String Unit Symbol} {goal : T}
    (proof : Derives .hoApply kb context goal naf) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  model.sound kb_models naf_adequate proof

theorem consistent : ¬ Derives .hoApply kb [] .falsity naf := model.consistent kb_models naf_adequate

end AnthillModKbSpec.InductionModel
