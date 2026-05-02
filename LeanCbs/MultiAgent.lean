import LeanCbs.Core

/-roots is the initial grant set of the Orchestrator.
 `CapChain roots c` says that capability `c` was derived from roots
 via a finite set of attenuating delegations. -/
inductive CapChain (roots : List Cap) : Cap → Prop where
  | base (c : Cap) (h : c ∈ roots) :
      CapChain roots c
  | step (parent child : Cap)
      (hchain : CapChain roots parent)
      (hatt   : Attenuates child parent) :
      CapChain roots child

/- Extending the orchestrator's grants never invalidates an existing chain-/
theorem CapChain.mono {roots₁ roots₂ : List Cap} {c : Cap}
    (hsub : roots₁ ⊆ roots₂)
    (h : CapChain roots₁ c) : CapChain roots₂ c := by
  induction h with
  | base c hm => exact .base c (hsub hm)
  | step p ch _ hatt ih => exact .step p ch ih hatt
