module

public import SteinerUpperBound.QueryProgram.Monad

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

variable {M Q R : Type*}

theorem Evaluates.accounted (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (o : Outcome R) (h : Evaluates m bits p o) :
    o.metricQueries + o.retentionQueries ≤ o.work ∧ o.positiveReplies ≤ o.retentionQueries := by
  have h₁ : p.evaluate m bits (fun r => ((r.metricQueries + r.retentionQueries : ℕ) : ℝ)) ≤
      p.evaluate m bits (fun r => (r.work : ℝ)) := by
    rw [← compile_expect, ← compile_expect]
    apply (p.compile m).law.expect_mono
    intro s
    dsimp only
    exact_mod_cast (SteinerUpperBound.QueryProgram.Code.accounted m bits p s).1
  have h₂ : p.evaluate m bits (fun r => (r.positiveReplies : ℝ)) ≤
      p.evaluate m bits (fun r => (r.retentionQueries : ℝ)) := by
    rw [← compile_expect, ← compile_expect]
    apply (p.compile m).law.expect_mono
    intro s
    dsimp only
    exact_mod_cast (SteinerUpperBound.QueryProgram.Code.accounted m bits p s).2
  rw [h, h] at h₁ h₂
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

end SteinerUpperBound.QueryProgram.Code
